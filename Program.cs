using AsmResolver.DotNet.Builder;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Serialized;
using AsmResolver.DotNet.Signatures.Types;
using AsmResolver.DotNet.Signatures;
using AsmResolver.DotNet;
using AsmResolver.IO;
using AsmResolver.PE.DotNet.Builder;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Strings;
using AsmResolver.PE.DotNet.Metadata.Tables.Rows;
using AsmResolver.PE.DotNet.Metadata.Tables;
using AsmResolver.PE.DotNet.Metadata.UserStrings;
using AsmResolver.PE.File;
using AsmResolver;
using System.Reflection;
using System.Security.Cryptography;
using System.Text;

namespace deobfuscator {


    internal class Deobfuscator {
        public ModuleDefinition module;
        public TablesStream tables;
        public StringsStream strings;
        public UserStringsStream userStrings;
        public Dictionary<MetadataToken, MethodDefinition> methodByToken;
        public PEFile pe;

        private FlareObfu1 obfu1;
        private FlareObfu2 obfu2;

        private string dstPath;

        public Deobfuscator(string srcPath, string dstPath) {
            this.dstPath = dstPath;
            methodByToken = new Dictionary<MetadataToken, MethodDefinition>();
            byte[] fileData = System.IO.File.ReadAllBytes(srcPath);
            var parameters = new ModuleReaderParameters(EmptyErrorListener.Instance);
            pe = PEFile.FromBytes(fileData);
            module = ModuleDefinition.FromFile(pe, parameters);
            tables = module.DotNetDirectory.Metadata.GetStream<TablesStream>();
            strings = module.DotNetDirectory.Metadata.GetStream<StringsStream>();
            userStrings = module.DotNetDirectory.Metadata.GetStream<UserStringsStream>();
            obfu1 = new FlareObfu1();
            obfu2 = new FlareObfu2();
        }

        public CallingConventions convertCC(CallingConventionAttributes attrs) {
            CallingConventions x = 0;
            if (attrs.HasFlag(CallingConventionAttributes.Default)) {
                x |= CallingConventions.Standard;
            }
            if (attrs.HasFlag(CallingConventionAttributes.VarArg)) {
                x |= CallingConventions.VarArgs;
            }
            if (attrs.HasFlag(CallingConventionAttributes.HasThis)) {
                x |= CallingConventions.HasThis;
            }
            if (attrs.HasFlag(CallingConventionAttributes.ExplicitThis)) {
                x |= CallingConventions.ExplicitThis;
            }
            return x;
        }

        public string computeFunctionSHA256(MethodDefinition method) {
            string localVariableString = "";
            string parameterInfoString = "";
            var rawBody = getRawBody(method);
            if (!rawBody.IsFat) {
                return "";
            }
            var fatBody = rawBody as CilRawFatMethodBody;
            var locals = getLocals(rawBody);
            var ma = (System.Reflection.MethodAttributes)(uint)method.Attributes;
            byte[] bytesMethodAttributes = Encoding.ASCII.GetBytes(ma.ToString());
            byte[] bytesReturnType = Encoding.ASCII.GetBytes(method.Signature.ReturnType.ToString());
            var cc = convertCC(method.Signature.Attributes);
            byte[] bytesCallingConvention = Encoding.ASCII.GetBytes(cc.ToString());
            foreach (var parameterInfo in method.Parameters) {
                var parameterType = parameterInfo.ParameterType;
                parameterInfoString += ((parameterType != null) ? parameterType.ToString() : null);
            }
            byte[] bytesMaxStack = Encoding.ASCII.GetBytes(fatBody.MaxStack.ToString());
            byte[] bytesOpcodes = BitConverter.GetBytes(fatBody.Code.GetPhysicalSize());
            foreach (var localVariableInfo in locals) {
                var localType = localVariableInfo.VariableType;
                localVariableString += ((localType != null) ? localType.ToString() : null);
            }
            byte[] bytesLocalVariables = Encoding.ASCII.GetBytes(localVariableString);
            byte[] bytesParameterInfos = Encoding.ASCII.GetBytes(parameterInfoString);
            IncrementalHash incrementalHash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
            incrementalHash.AppendData(bytesOpcodes);
            incrementalHash.AppendData(bytesMethodAttributes);
            incrementalHash.AppendData(bytesReturnType);
            incrementalHash.AppendData(bytesMaxStack);
            incrementalHash.AppendData(bytesLocalVariables);
            incrementalHash.AppendData(bytesParameterInfos);
            incrementalHash.AppendData(bytesCallingConvention);
            byte[] hashAndReset = incrementalHash.GetHashAndReset();
            StringBuilder stringBuilder = new StringBuilder(hashAndReset.Length * 2);
            for (int j = 0; j < hashAndReset.Length; j++) {
                stringBuilder.Append(hashAndReset[j].ToString("x2"));
            }
            return stringBuilder.ToString();
        }

        public byte[] rc4(byte[] input) {
            byte[] key = new byte[] { 18, 120, 171, 223 };
            int[] table = new int[256];
            byte[] output = new byte[input.Length];
            int i;
            int a;
            int b;
            for (i = 0; i < 256; i++) {
                table[i] = i;
            }
            for (i = (a = 0); i < 256; i++) {
                a = (a + table[i] + key[i & 3]) % 256;
                int num2 = table[i];
                table[i] = table[a];
                table[a] = num2;
            }
            a = (b = (i = 0));
            while (i < input.Length) {
                b++;
                b %= 256;
                a += table[b];
                a %= 256;
                int temp = table[b];
                table[b] = table[a];
                table[a] = temp;
                int blockKey = table[(table[b] + table[a]) % 256];
                output[i] = (byte)((int)input[i] ^ blockKey);
                i++;
            }
            return output;
        }

        private void deobfuscateMethod(MethodDefinition method, byte[] code) {
            var fm = new CilMethodBody(method);
            var opResolver = new PhysicalCilOperandResolver(module, fm);
            var newDasm = new CilDisassembler(ByteArrayDataSource.CreateReader(code), opResolver);
            var body = new CilMethodBody(method);
            body.Instructions.Clear();
            foreach (var v in getLocals(getRawBody(method))) {
                body.LocalVariables.Add(v);
            }
            foreach (var instruction in newDasm.ReadInstructions()) {
                body.Instructions.Add(instruction);
            }
            method.CilMethodBody = body;
        }

        public uint unpackInt(byte[] b, uint j) {
            uint unpacked = 0;
            unpacked += (uint)b[j + 3] * 0x1000000;
            unpacked += (uint)b[j + 2] * 0x10000;
            unpacked += (uint)b[j + 1] * 0x100;
            unpacked += (uint)b[j + 0];
            return unpacked;
        }

        public byte[] readCodeFromSection(PESection section) {
            byte[] sectionData = new byte[section.GetVirtualSize()];
            section.CreateReader().ReadBytes(sectionData, 0, (int)section.GetVirtualSize());
            byte[] b = rc4(sectionData);
            uint j = 0;
            while (j < b.Length) {
                uint num = 0;
                if (b[j] == 254) {
                    num = 65024U + (uint)b[j + 1];
                    j++;
                } else {
                    num = (uint)b[j];
                }
                j++;
                if (!obfu2.dictionary.ContainsKey(num)) {
                    throw new Exception("Invalid opcode");
                }
                var op = obfu2.dictionary[num];
                switch (op) {
                    case OT.B:
                        uint t = unpackInt(b, j);
                        t ^= 2727913149U;
                        b[j + 0] = (byte)(t >> 0x00);
                        b[j + 1] = (byte)(t >> 0x08);
                        b[j + 2] = (byte)(t >> 0x10);
                        b[j + 3] = (byte)(t >> 0x18);
                        j += 4;
                        break;
                    case OT.C:
                    case OT.E:
                        j++;
                        break;
                    case OT.D:
                    case OT.G:
                        j += 4;
                        break;
                    case OT.F:
                        j += 2;
                        break;
                    case OT.H:
                        j += 8;
                        break;
                    case OT.I:
                        j += 4 + unpackInt(b, j) * 4;
                        break;
                }
            }
            return b;
        }

        public void deobfuscate() {

            uint hashDeobfuscations = 0;
            var sections = new HashSet<PESection>();
            foreach (var section in pe.Sections) {
                sections.Add(section);
            }

            forAllMethods(method => {
                methodByToken.Add(method.MetadataToken, method);
                string h = computeFunctionSHA256(method);
                foreach (var section in pe.Sections) {
                    if (section.Name.StartsWith(".")) {
                        sections.Remove(section);
                        continue;
                    }
                    if (h.StartsWith(section.Name)) {
                        byte[] b = null;
                        bool ok = true;
                        try {
                            b = readCodeFromSection(section);
                        } catch {
                            ok = false;
                            Console.WriteLine("failed to patch {0} into {1}",
                                    section.Name, method.Name);
                        }
                        if (ok) {
                            deobfuscateMethod(method, b);
                            hashDeobfuscations += 1;
                            Console.WriteLine("patched section {0} into {1}; sizes {2} vs {3}",
                                section.Name, method.Name, section.GetVirtualSize(), getRawBody(method).Code.GetVirtualSize());
                        }
                        sections.Remove(section);
                        break;
                    }
                }
                return true;
            });

            foreach (var method in getAllCallers(0x060000BC)) {
                var obfuscatedMethod = getFirstCall(method);
                var prefix = getFieldPrefix(method, "_b");
                var b = obfu1.GetB(prefix);
                var m = obfu1.GetM(prefix);
                foreach (KeyValuePair<uint, int> keyValuePair in m) {
                    uint num = (uint)keyValuePair.Value;
                    uint key = keyValuePair.Key;
                    b[(int)(key + 0U)] = (byte)(num >> 0x00);
                    b[(int)(key + 1U)] = (byte)(num >> 0x08);
                    b[(int)(key + 2U)] = (byte)(num >> 0x10);
                    b[(int)(key + 3U)] = (byte)(num >> 0x18);
                }
                deobfuscateMethod(obfuscatedMethod, b);
                Console.WriteLine("patched layer1 function {0} ({1})", obfuscatedMethod.Name, obfuscatedMethod.MetadataToken);
            }

            foreach (var section in sections) {
                bool ok = false;
                var candidates = new List<MethodDefinition>();

                forAllMethods(method => {
                    if (!method.Name.ToString().StartsWith("flare"))
                        return true;
                    var body = getRawBody(method);
                    if (body.Code.GetVirtualSize() != section.GetVirtualSize())
                        return true;
                    try {
                        var i = method.CilMethodBody.Instructions;
                        if (i.Count > 0) {
                            candidates.Add(method);
                        }
                    } catch {
                        try {
                            var b = readCodeFromSection(section);
                            deobfuscateMethod(method, b);
                            Console.WriteLine("{0} with virtual size 0x{1:x4}: patched from section {2} with same size",
                                    method.Name, section.GetVirtualSize(), section.Name);
                            ok = true;
                        } catch {
                            ok = false;
                        }
                    }
                    return true;
                });

                if (!ok) {
                    if (candidates.Count > 0) {
                        var method = candidates.Last();
                        var b = readCodeFromSection(section);
                        deobfuscateMethod(method, b);
                        Console.WriteLine("{0} with virtual size 0x{1:x4}: patched from section {2} with same size as only candidate",
                            method.Name, section.GetVirtualSize(), section.Name);
                        ok = true;
                    }
                }

                if (!ok) {
                    Console.WriteLine("section {0} with virtual size 0x{1:x6}: {2} candidates found",
                        section.Name, section.GetVirtualSize(), candidates.Count);
                    foreach (var c in candidates) {
                        Console.WriteLine("   -> {0}", c.Name);
                    }
                } else {
                    sections.Remove(section);
                }
            }

            Console.WriteLine("hash-patched {0} functions, {1} sections remained", hashDeobfuscations, sections.Count);
            foreach (var section in sections) {
                Console.WriteLine("opcode section remains with size {0}", section.GetVirtualSize());
                try {
                    readCodeFromSection(section);
                } catch {
                    Console.WriteLine("... but it is probably the main payload");
                }
            }

            dumpImage();
        }

        private void dumpImage() {
            var imageBuilder = new ManagedPEImageBuilder();
            var factory = new DotNetDirectoryFactory();
            factory.MetadataBuilderFlags = MetadataBuilderFlags.PreserveAll;
                // | MetadataBuilderFlags.NoStringsStreamOptimization;
            imageBuilder.DotNetDirectoryFactory = factory;

            var result = imageBuilder.CreateImage(module);

            Console.WriteLine("Construction finished with {0} errors.", result.DiagnosticBag.Exceptions.Count);

            if (!result.DiagnosticBag.IsFatal) {
                var image = result.ConstructedImage;
                var fileBuilder = new ManagedPEFileBuilder();
                var file = fileBuilder.CreateFile(image);
                file.Write(dstPath);
            } else {
                Console.WriteLine("Fatal Error.");
            }
        }

        private CilRawMethodBody getRawBody(MethodDefinition method) {
            var tblStream = module.DotNetDirectory.Metadata.GetStream<TablesStream>();
            var methodDfn = tblStream.GetTable<MethodDefinitionRow>();
            var methodRow = methodDfn.GetByRid(method.MetadataToken.Rid);
            var reader = methodRow.Body.CreateReader();
            return CilRawMethodBody.FromReader(ref reader);
        }

        private List<CilLocalVariable> getLocals(CilRawMethodBody body) {
            var variables = new List<CilLocalVariable>();
            if (body is CilRawFatMethodBody fatBody) {
                if (fatBody.LocalVarSigToken != MetadataToken.Zero && module.TryLookupMember(fatBody.LocalVarSigToken, out var member)) {
                    StandAloneSignature standAloneSignature = member as StandAloneSignature;
                    if (standAloneSignature != null) {
                        var lv = standAloneSignature.Signature as LocalVariablesSignature;
                        if (lv != null) {
                            IList<TypeSignature> variableTypes = lv.VariableTypes;
                            for (int i = 0; i < variableTypes.Count; i++) {
                                variables.Add(new CilLocalVariable(variableTypes[i]));
                            }
                        }
                    }
                }
            }
            return variables;
        }

        private MethodDefinition getFirstCall(MethodDefinition method) {
            foreach (var instruction in method.CilMethodBody.Instructions) {
                if (instruction.OpCode.OperandType != CilOperandType.InlineMethod)
                    continue;
                if (instruction.Operand is IMethodDescriptor) {
                    MetadataToken t = ((IMethodDescriptor)instruction.Operand).MetadataToken;
                    return methodByToken[t];
                }
            }
            throw new Exception("Method not found");
        }

        private string getFieldPrefix(MethodDefinition method, string suffix) {
            foreach (var instruction in method.CilMethodBody.Instructions) {
                if (instruction.OpCode.OperandType != CilOperandType.InlineField)
                    continue;
                if (instruction.Operand is IFieldDescriptor) {
                    MetadataToken t = ((IFieldDescriptor)instruction.Operand).MetadataToken;
                    MetadataTable<FieldDefinitionRow> fieldTable = tables.GetTable<FieldDefinitionRow>();
                    string value = strings.GetStringByIndex(fieldTable.GetByRid(t.Rid).Name);
                    if (value != null && value.EndsWith(suffix)) {
                        return value.Substring(0, value.Length - suffix.Length);
                    }
                }
            }
            throw new Exception(
                String.Format("Field with suffix '{0}' was not found in {1}", suffix, method.Name));
        }

        private List<MethodDefinition> getAllCallers(int token) {
            List<MethodDefinition> callers = new List<MethodDefinition>();
            forAllTypes(type => {
                foreach (var method in type.Methods) {
                    try {
                        if (method.CilMethodBody == null)
                            continue;
                        if (method.CilMethodBody.Instructions == null)
                            continue;
                        foreach (var instruction in method.CilMethodBody.Instructions) {
                            if (instruction.OpCode.OperandType != CilOperandType.InlineMethod)
                                continue;
                            if (instruction.Operand is IMethodDescriptor) {
                                MetadataToken t = ((IMethodDescriptor)instruction.Operand).MetadataToken;
                                if (t.ToUInt32() == token) {
                                    callers.Add(method);
                                    break;
                                }
                            }
                        }
                    } catch {
                        continue;
                    }
                }
                return true;
            });
            return callers;
        }
        void forAllMethods(Predicate<MethodDefinition> action) {
            forAllTypes(type => {
                foreach (var method in type.Methods) {
                    if (!action(method)) {
                        return false;
                    }
                }
                return true;
            });
        }

        void forAllTypes(Predicate<TypeDefinition> action) {
            void _recurse(IEnumerable<TypeDefinition> types) {
                foreach (var type in types) {
                    if (!action(type)) {
                        break;
                    }
                    _recurse(type.NestedTypes);
                }
            }
            _recurse(module.TopLevelTypes);
        }
    }


    internal class Program {
        static void Main(string[] args) {
            if (args.Length != 2) {
                Console.WriteLine("usage: {0} <InputFile> <OutputFile>", 
                    System.AppDomain.CurrentDomain.FriendlyName);
                return;
            }
            Deobfuscator d = new Deobfuscator(args[0], args[1]);
            d.deobfuscate();
        }
    }
}

