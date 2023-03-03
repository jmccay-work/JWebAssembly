/*
   Copyright 2018 - 2022 Volker Berlin (i-net software)

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

*/
package de.inetsoftware.jwebassembly.module;

import static de.inetsoftware.jwebassembly.module.WasmCodeBuilder.CONSTRUCTOR;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.ToIntFunction;

import javax.annotation.Nonnull;

import de.inetsoftware.classparser.BootstrapMethod;
import de.inetsoftware.classparser.ClassFile;
import de.inetsoftware.classparser.ClassFile.Type;
import de.inetsoftware.classparser.ConstantClass;
import de.inetsoftware.classparser.ConstantRef;
import de.inetsoftware.classparser.FieldInfo;
import de.inetsoftware.classparser.MethodInfo;
import de.inetsoftware.jwebassembly.JWebAssembly;
import de.inetsoftware.jwebassembly.WasmException;
import de.inetsoftware.jwebassembly.wasm.AnyType;
import de.inetsoftware.jwebassembly.wasm.ArrayType;
import de.inetsoftware.jwebassembly.wasm.LittleEndianOutputStream;
import de.inetsoftware.jwebassembly.wasm.NamedStorageType;
import de.inetsoftware.jwebassembly.wasm.StructOperator;
import de.inetsoftware.jwebassembly.wasm.ValueType;
import de.inetsoftware.jwebassembly.wasm.ValueTypeParser;
import de.inetsoftware.jwebassembly.watparser.WatParser;

/**
 * Manage the written and to write types (classes)
 * 
 * @author Volker Berlin
 */
public class TypeManager {
    /**
     * Constant for an empty string ("") to save memory.
     */
    private static final String             EMPTY_STRING                       = "";

    /** name of virtual function table, start with a point for an invalid Java identifier */
    static final String                     FIELD_VTABLE                       = ".vtable";

    /**
     * Name of field with system hash code, start with a point for an invalid Java identifier.
     */
    static final String                     FIELD_HASHCODE                     = ".hashcode";

    /**
     * Name of field with array value.
     */
    public static final String              FIELD_VALUE                        = ".array";

    /**
     * Byte position in the type description that contains the offset to the interfaces. Length 4 bytes.
     */
    public static final int                 TYPE_DESCRIPTION_INTERFACE_OFFSET  = 0;

    /**
     * Byte position in the type description that contains the offset to the instanceof list. Length 4 bytes.
     */
    public static final int                 TYPE_DESCRIPTION_INSTANCEOF_OFFSET = 4;

    /**
     * Byte position in the type description that contains the offset to class name idx in the string constant table.
     * Length 4 bytes.
     */
    public static final int                 TYPE_DESCRIPTION_TYPE_NAME         = 8;

    /**
     * Byte position in the type description that contains the type of the array (component type). Length 4 bytes.
     */
    public static final int                 TYPE_DESCRIPTION_ARRAY_TYPE        = 12;

    /**
     * Byte position in the type description that contains the offset to the fields. Length 4 bytes.
     */
    public static final int                 TYPE_DESCRIPTION_FIELDS_OFFSET     = 16;

    /**
     * The reserved index position of the first function in the vtable. For performance reasons the first function does not have the index 0 but this index.
     * For the byte offset you have to multiply it by 4.
     * <li>offset of interface call table (itable)
     * <li>offset of instanceof list
     * <li>offset of class name idx in the string constant table
     * <li>array component type
     * <li>offset of fields description
     */
    private static final int                VTABLE_FIRST_FUNCTION_INDEX        = 5;

    private static final FunctionName       CLASS_CONSTANT_FUNCTION            = new FunctionName( "java/lang/Class.classConstant(I)Ljava/lang/Class;" );

    /**
     * Type id of primitive class
     */
    public static final int                 BOOLEAN                            = 0;

    /**
     * Type id of primitive class
     */
    public static final int                 BYTE                               = 1;

    /**
     * Type id of primitive class
     */
    public static final int                 CHAR                               = 2;

    /**
     * Type id of primitive class
     */
    public static final int                 DOUBLE                             = 3;

    /**
     * Type id of primitive class
     */
    public static final int                 FLOAT                              = 4;

    /**
     * Type id of primitive class
     */
    public static final int                 INT                                = 5;

    /**
     * Type id of primitive class
     */
    public static final int                 LONG                               = 6;

    /**
     * Type id of primitive class
     */
    public static final int                 SHORT                              = 7;

    /**
     * Type id of primitive class
     */
    public static final int                 VOID                               = 8;

    /**
     * the list of primitive types. The order is important and must correlate with getPrimitiveClass.
     * 
     * @see ReplacementForClass#getPrimitiveClass(String)
     */
    private static final String[]           PRIMITIVE_CLASSES                  =
                    { "boolean", "byte", "char", "double", "float", "int", "long", "short", "void" };

    private final Map<Object, StructType>   structTypes                        = new LinkedHashMap<>();

    private final Map<BlockType, BlockType> blockTypes                         = new LinkedHashMap<>();

    private int                             typeIndexCounter;

    private boolean                         isFinish;

    final WasmOptions                       options;

    private int                             typeTableOffset;

    private ClassFileLoader                 classFileLoader;

    /**
     * Initialize the type manager.
     * 
     * @param options
     *            compiler properties
     */
    TypeManager( WasmOptions options ) {
        this.options = options;
    }

    /**
     * Initialize the type manager
     * 
     * @param classFileLoader
     *            for loading the class files
     */
    void init( ClassFileLoader classFileLoader ) {
        this.classFileLoader = classFileLoader;
    }

    /**
     * Count of used types
     * 
     * @return the count
     */
    public int size() {
        return structTypes.size();
    }

    /**
     * If the scan phase is finish
     * 
     * @return true, if scan phase is finish
     */
    boolean isFinish() {
        return isFinish;
    }

    /**
     * Scan the hierarchy of the types.
     * 
     * @throws IOException
     *             if any I/O error occur on loading or writing
     */
    void scanTypeHierarchy() throws IOException {
        for( StructType type : new ArrayList<>( structTypes.values() ) ) {
            type.scanTypeHierarchy( options.functions, this, classFileLoader );
        }
    }

    /**
     * Finish the prepare and write the types. Now no new types and functions should be added.
     * 
     * @param writer
     *            the targets for the types
     * @throws IOException
     *             if any I/O error occur on loading or writing
     */
    void prepareFinish( ModuleWriter writer ) throws IOException {
        isFinish = true;
        for( StructType type : structTypes.values() ) {
            type.writeStructType( writer );
        }

        for( BlockType type : blockTypes.values() ) {
            type.code = writer.writeBlockType( type );
        }

        // write type table
        @SuppressWarnings( "resource" )
        LittleEndianOutputStream dataStream = new LittleEndianOutputStream( writer.dataStream );
        typeTableOffset = writer.dataStream.size();
        for( StructType type : structTypes.values() ) {
            dataStream.writeInt32( type.vtableOffset );
        }
    }

    /**
     * Create an accessor for typeTableOffset and mark it.
     * 
     * @return the function name
     */
    WatCodeSyntheticFunctionName getTypeTableMemoryOffsetFunctionName() {
        WatCodeSyntheticFunctionName offsetFunction =
                        new WatCodeSyntheticFunctionName( "java/lang/Class", "typeTableMemoryOffset", "()I", EMPTY_STRING, null, ValueType.i32 ) {
                            @Override
                            protected String getCode() {
                                return String.format("i32.const %d", typeTableOffset);
                            }
                        };
        options.functions.addReplacement( offsetFunction, null );
        return offsetFunction;
    }

    /**
     * Get the function name to get a constant class.
     * 
     * @return the function
     */
    @Nonnull
    FunctionName getClassConstantFunction() {
        return CLASS_CONSTANT_FUNCTION;
    }

    /**
     * Check the internal state of the manager and create initial classes.
     * 
     * @param newType
     *            the requested type for debug output
     */
    private void checkStructTypesState( Object newType ) {
        JWebAssembly.LOGGER.fine( String.format("\t\ttype: %s", newType) );
        if( isFinish ) {
            throw new WasmException( String.format("Register needed type after scanning: %s", newType), -1 );
        }

        if( structTypes.isEmpty() ) {
            for( String primitiveTypeName : PRIMITIVE_CLASSES ) {
                structTypes.put( primitiveTypeName, new StructType( primitiveTypeName, StructTypeKind.primitive, this ) );
            }
        }
    }

    /**
     * Get the StructType. If needed an instance is created.
     * 
     * @param name
     *            the type name like java/lang/Object
     * @return the struct type
     */
    @Nonnull
    public StructType valueOf( String name ) {
        StructType type = structTypes.get( name );
        if( type == null ) {
            if( name.startsWith( "[" ) ) {
                return (StructType)new ValueTypeParser( name, options.types ).next();
            } else {
                checkStructTypesState( name );
                type = new StructType( name, StructTypeKind.normal, this );
            }

            structTypes.put( name, type );
        }
        return type;
    }

    /**
     * Get the array type for the given component type.
     * 
     * @param arrayType
     *            the component type of the array
     * @return the array type
     */
    @Nonnull
    public ArrayType arrayType( AnyType arrayType ) {
        ArrayType type = (ArrayType)structTypes.get( arrayType );
        if( type == null ) {
            checkStructTypesState( arrayType );

            int componentClassIndex;
            if( !arrayType.isRefType() ) {
                // see ReplacementForClass.getPrimitiveClass(String)
                switch( (ValueType)arrayType ) {
                    case bool:
                        componentClassIndex = 0;
                        break;
                    case i8:
                        componentClassIndex = 1;
                        break;
                    case u16:
                        componentClassIndex = 2;
                        break;
                    case f64:
                        componentClassIndex = 3;
                        break;
                    case f32:
                        componentClassIndex = 4;
                        break;
                    case i32:
                        componentClassIndex = 5;
                        break;
                    case i64:
                        componentClassIndex = 6;
                        break;
                    case i16:
                        componentClassIndex = 7;
                        break;
                    case eqref:
                    case externref:
                        componentClassIndex = valueOf( "java/lang/Object" ).classIndex;
                        break;
                    default:
                        throw new WasmException( String.format("Not supported array type: %s", arrayType), -1 );
                }
            } else {
                componentClassIndex = ((StructType)arrayType).classIndex;
            }

            type = new ArrayType( arrayType, this, componentClassIndex, options );
            if( options.useGC() ) {
                StructType nativeArrayType = (StructType)type.getNativeArrayType();
                structTypes.put( nativeArrayType.getName(), nativeArrayType );
            }
            structTypes.put( arrayType, type );
        }
        return type;
    }

    /**
     * Create a lambda type
     * 
     * @param method
     *            the name BootstrapMethod from the parsed class file
     * @param factorySignature
     *            Get the signature of the factory method. For example "()Ljava.lang.Runnable;" for the lambda expression
     *            <code>Runnable run = () -&gt; foo();</code>
     * @param interfaceMethodName
     *            the name of the implemented method in the interface
     * @param lineNumber
     *            the line number in the Java source code
     * @return the type
     */
    LambdaType lambdaType( @Nonnull BootstrapMethod method, String factorySignature, String interfaceMethodName, int lineNumber ) {
        ConstantRef implMethod = method.getImplMethod();
        FunctionName syntheticLambdaFunctionName = new FunctionName( implMethod );

        Iterator<AnyType> parser = new ValueTypeParser( factorySignature, this );
        ArrayList<AnyType> params = new ArrayList<>();
        do {
            AnyType param = parser.next();
            if( param == null ) {
                break;
            }
            params.add( param );
        } while( true );
        StructType interfaceType = (StructType)parser.next();

        String typeName = String.format("%s$$%s/%d", implMethod.getClassName(), implMethod.getName(), Math.abs( implMethod.getName().hashCode() ));

        LambdaType type = (LambdaType)structTypes.get( typeName );
        if( type == null ) {
            type = new LambdaType( typeName, method, params, interfaceType, syntheticLambdaFunctionName, interfaceMethodName, this, lineNumber );

            structTypes.put( typeName, type );
        }
        return type;
    }

    /**
     * Create block type
     * 
     * @param params
     *            the parameters
     * @param results
     *            the results
     * @return the type
     */
    @Nonnull
    BlockType blockType( List<AnyType> params, List<AnyType> results ) {
        BlockType blockType = new BlockType( params, results );
        BlockType type = blockTypes.get( blockType );
        if( type != null ) {
            return type;
        }
        blockTypes.put( blockType, blockType );
        return blockType;
    }

    /**
     * Create the FunctionName for a virtual call. The function has 2 parameters (THIS, virtualfunctionIndex) and
     * returns the index of the function.
     * 
     * @return the name
     */
    @Nonnull
    WatCodeSyntheticFunctionName createCallVirtual() {
        StringBuffer sb = new StringBuffer(1024);
        return new WatCodeSyntheticFunctionName( //
                        "callVirtual", 
                                    sb.append("local.get 0 ") // THIS
                                      .append("struct.get java/lang/Object .vtable ") // vtable is on index 0
                                      .append("local.get 1 ") // virtualFunctionIndex
                                      .append("i32.add ") //
                                      .append("i32.load offset=0 align=4 ") //
                                      .append("return ") //
                                      .toString(), 
                  valueOf( "java/lang/Object" ), ValueType.i32, null, ValueType.i32 ); // THIS, virtualfunctionIndex, returns functionIndex
    }

    /**
     * Create the FunctionName for a interface call. The function has 3 parameters (THIS,classIndex,
     * virtualfunctionIndex) and returns the index of the function.
     * 
     * @return the name
     */
    @Nonnull
    WatCodeSyntheticFunctionName createCallInterface() {
        /*
        static int callInterface( OBJECT THIS, int classIndex, int virtualfunctionIndex ) {
            int table = THIS.vtable;
            table += i32_load[table];
        
            do {
                int nextClass = i32_load[table];
                if( nextClass == classIndex ) {
                    return i32_load[table + virtualfunctionIndex];
                }
                if( nextClass == 0 ) {
                    return -1;//throw new NoSuchMethodError();
                }
                table += i32_load[table + 4];
            } while( true );
        }
         */
        StringBuffer sb = new StringBuffer(1024);
        return new WatCodeSyntheticFunctionName( //
                        "callInterface", 
                            // TODO: all these strings should be refactored to 1 string to avoid creating so many String objects.
                          sb.append("local.get 0 ") // $THIS
                            .append("struct.get java/lang/Object .vtable ") // vtable is on index 0
                            .append("local.tee 3 ") // save $table
                            .append(String.format("i32.load offset=%d align=4 ", TYPE_DESCRIPTION_INTERFACE_OFFSET)) // get offset of itable (int position 0, byte position 0)
                            .append("local.get 3 ") // save $table
                            .append("i32.add ") // $table += i32_load[$table]
                            .append("local.set 3 ") // save $table, the itable start location
                            .append("loop") //
                            .append("  local.get 3") // get $table
                            .append("  i32.load offset=0 align=4  local.tee 4") // save $nextClass
                            .append("  local.get 1") // get $classIndex
                            .append("  i32.eq") //
                            .append("  if") // $nextClass == $classIndex
                            .append("    local.get 3") // get $table
                            .append("    local.get 2") // get $virtualfunctionIndex
                            .append("    i32.add") // $table + $virtualfunctionIndex
                            .append("    i32.load offset=0 align=4") // get the functionIndex
                            .append("    return") //
                            .append("  end") //
                            .append("  local.get 4") // save $nextClass
                            .append("  i32.eqz") //
                            .append("  if") // current offset == end offset
                            .append("    unreachable") // TODO throw a ClassCastException if exception handling is supported
                            .append("  end") //
                            .append("  local.get 3") // get $table
                            .append("  i32.const 4") //
                            .append("  i32.add") // $table + 4
                            .append("  i32.load offset=0 align=4") // get the functionIndex
                            .append("  local.get 3") // $table
                            .append("  i32.add") // $table += i32_load[table + 4];
                            .append("  local.set 3") // set $table
                            .append("  br 0 ") //
                            .append("end ") //
                            .append("unreachable") // should never reach
                            .toString(), valueOf( "java/lang/Object" ), ValueType.i32, ValueType.i32, null, ValueType.i32 ); // THIS, classIndex, virtualfunctionIndex, returns functionIndex
    }

    /**
     * Create the FunctionName for the INSTANCEOF operation and mark it as used. The function has 2 parameters (THIS,
     * classIndex) and returns true if there is a match.
     * 
     * @return the name
     */
    WatCodeSyntheticFunctionName createInstanceOf() {
        StringBuffer sb = new StringBuffer(1024);
        return new WatCodeSyntheticFunctionName( //
                        "instanceof", 
                             sb.append("local.get 0 ") // THIS
                               .append("ref.is_null if i32.const 0 return end ") // NULL check
                               .append("local.get 0 ") // THIS
                               .append("struct.get java/lang/Object .vtable ") // vtable is on index 0
                               .append("local.tee 2 ") // save the vtable location
                               .append(String.format("i32.load offset=%d align=4 ", TYPE_DESCRIPTION_INSTANCEOF_OFFSET)) // get offset of instanceof inside vtable (int position 1, byte position 4)
                               .append("local.get 2 ") // get the vtable location
                               .append("i32.add ") //
                               .append("local.tee 2 ") // save the instanceof location
                               .append("i32.load offset=0 align=4 ") // count of instanceof entries
                               .append("i32.const 4 ") //
                               .append("i32.mul ") //
                               .append("local.get 2 ") // get the instanceof location
                               .append("i32.add ") //
                               .append("local.set 3 ") // save end position
                               .append("loop") //
                               .append("  local.get 2 ") // get the instanceof location pointer
                               .append("  local.get 3 ") // get the end location
                               .append("  i32.eq") //
                               .append("  if") // current offset == end offset
                               .append("    i32.const 0") // not found
                               .append("    return") //
                               .append("  end") //
                               .append("  local.get 2") // get the instanceof location pointer
                               .append("  i32.const 4") //
                               .append("  i32.add") // increment offset
                               .append("  local.tee 2") // save the instanceof location pointer
                               .append("  i32.load offset=0 align=4") //
                               .append("  local.get 1") // the class index that we search
                               .append("  i32.ne") //
                               .append("  br_if 0 ") //
                               .append("end ") //
                               .append("i32.const 1 ") // class/interface found
                               .append("return ") //
                               .toString(), 
                valueOf( "java/lang/Object" ), ValueType.i32, null, ValueType.i32 ); // THIS, classIndex, returns boolean
    }

    /**
     * Create the FunctionName for the CAST operation and mark it as used. The function has 2 parameters (THIS,
     * classIndex) and returns this if the type match else it throw an exception.
     * 
     * @return the name
     */
    WatCodeSyntheticFunctionName createCast() {
        StringBuffer sb = new StringBuffer(1024);
        return new WatCodeSyntheticFunctionName( //
                        "cast", 
                            sb.append("local.get 0 ") // THIS
                                  .append("ref.is_null if local.get 0 return end ") // NULL check
                                  .append("local.get 0 ") // THIS
                                  .append("local.get 1 ") // the class index that we search
                                  .append("call $.instanceof()V ") // the synthetic signature of ArraySyntheticFunctionName
                                  .append("if ") //
                                  .append("  local.get 0 ") // THIS
                                  .append("  return ") //
                                  .append("end ") //
                                  .append("unreachable ") // TODO throw a ClassCastException if exception handling is supported
                                  .toString(), 
                valueOf( "java/lang/Object" ), ValueType.i32, null, valueOf( "java/lang/Object" ) );
    }

    /**
     * The kind of type
     * 
     * @author Volker Berlin
     */
    public static enum StructTypeKind {
        primitive, normal, array, array_native, lambda;
    }

    /**
     * A reference to a type.
     * 
     * @author Volker Berlin
     */
    public static class StructType implements AnyType {

        private final String                        name;

        private final StructTypeKind                kind;

        private final TypeManager                   manager;

        private final int                           classIndex;

        private int                                 code         = Integer.MAX_VALUE;

        private HashSet<String>                     neededFields = new HashSet<>();

        private List<NamedStorageType>              fields;

        private List<FunctionName>                  vtable;

        private Set<StructType>                     instanceOFs;

        private Map<StructType, List<FunctionName>> interfaceMethods;

        /**
         * The offset to the vtable in the data section.
         */
        private int                                 vtableOffset;

        /**
         * Create a reference to type
         * 
         * @param name
         *            the Java class name like "java/lang/String"
         * @param kind
         *            the type kind
         * @param manager
         *            the manager which hold all StructTypes
         */
        protected StructType( @Nonnull String name, @Nonnull StructTypeKind kind, @Nonnull TypeManager manager ) {
            this.name = name;
            this.kind = kind;
            this.manager = manager;
            switch( kind ) {
                case array_native:
                    this.classIndex = -1;
                    break;
                default:
                    this.classIndex = manager.typeIndexCounter++;
            }
        }

        /**
         * Mark that the field was used in any getter or setter.
         * 
         * @param fieldName
         *            the name of the field
         */
        void useFieldName( NamedStorageType fieldName ) {
            neededFields.add( fieldName.getName() );
        }

        /**
         * Write this struct type and initialize internal structures
         * 
         * @param functions
         *            the used functions for the vtables of the types
         * @param types
         *            for types of fields
         * @param classFileLoader
         *            for loading the class files
         * @throws IOException
         *             if any I/O error occur on loading or writing
         */
        private void scanTypeHierarchy( FunctionManager functions, TypeManager types, ClassFileLoader classFileLoader ) throws IOException {
            JWebAssembly.LOGGER.fine( String.format("scan type hierachy: %s", name) );
            fields = new ArrayList<>();
            vtable = new ArrayList<>();
            instanceOFs = new LinkedHashSet<>(); // remembers the order from bottom to top class.
            instanceOFs.add( this );
            interfaceMethods = new LinkedHashMap<>();
            switch( kind ) {
                case primitive:
                    // nothing
                    break;
                case array:
                    HashSet<String> allNeededFields = new HashSet<>();
                    listStructFields( "java/lang/Object", functions, types, classFileLoader, allNeededFields );
                    fields.add( ((ArrayType)this).getNativeFieldName() );
                    break;
                case array_native:
                    fields.add( new NamedStorageType( ((ArrayType)this).getArrayType(), null, null ) );
                    break;
                case lambda:
                    allNeededFields = new HashSet<>();
                    listStructFields( "java/lang/Object", functions, types, classFileLoader, allNeededFields );
                    LambdaType lambda = (LambdaType)this;
                    fields.addAll( lambda.getParamFields() );
                    List<FunctionName> iMethods = new ArrayList<>();
                    iMethods.add( lambda.getLambdaMethod() );
                    interfaceMethods.put( lambda.getInterfaceType(), iMethods );
                    functions.setITableIndex( new FunctionName( lambda.getInterfaceType().name, lambda.getInterfaceMethodName(), lambda.getLambdaMethod().signature ), 2 );
                    break;
                default:
                    // add all interfaces to the instanceof set
                    listInterfaces( functions, types, classFileLoader );

                    allNeededFields = new HashSet<>();
                    listStructFields( name, functions, types, classFileLoader, allNeededFields );
            }
        }

        /**
         * Write this struct type and initialize internal structures
         * 
         * @param writer
         *            the targets for the types
         * @throws IOException
         *             if any I/O error occur on loading or writing
         */
        private void writeStructType( ModuleWriter writer ) throws IOException {
            JWebAssembly.LOGGER.fine( String.format("write type: %s", name) );
            code = writer.writeStructType( this );
        }

        /**
         * List the non static fields of the class and its super classes.
         * 
         * @param className
         *            the className to list. because the recursion this must not the name of this class
         * @param functions
         *            the used functions for the vtables of the types
         * @param types
         *            for types of fields
         * @param classFileLoader
         *            for loading the class files
         * @param allNeededFields
         *            for recursive call list this all used fields
         * @throws IOException
         *             if any I/O error occur on loading or writing
         */
        private void listStructFields( String className, FunctionManager functions, TypeManager types, ClassFileLoader classFileLoader, HashSet<String> allNeededFields ) throws IOException {
            ClassFile classFile = classFileLoader.get( className );
            if( classFile == null ) {
                throw new WasmException( String.format("Missing class: %s", className), -1 );
            }

            // interface does not need to resolve
            if( classFile.getType() == Type.Interface ) {
                // to make it possible to cast an interface to java/lang/Object it must have the same fileds also if we never create an instance
                fields.add( new NamedStorageType( ValueType.i32, className, FIELD_VTABLE ) );
                fields.add( new NamedStorageType( ValueType.i32, className, FIELD_HASHCODE ) );
                return;
            }

            {
                // list all used fields
                StructType type = types.structTypes.get( className );
                if( type != null ) {
                    allNeededFields.addAll( type.neededFields );
                    instanceOFs.add( type );
                }
            }

            // List stuff of super class
            ConstantClass superClass = classFile.getSuperClass();
            if( superClass != null ) {
                String superClassName = superClass.getName();
                listStructFields( superClassName, functions, types, classFileLoader, allNeededFields );
            } else {
                fields.add( new NamedStorageType( ValueType.i32, className, FIELD_VTABLE ) );
                fields.add( new NamedStorageType( ValueType.i32, className, FIELD_HASHCODE ) );
            }

            // list all fields
            for( FieldInfo field : classFile.getFields() ) {
                if( field.isStatic() ) {
                    continue;
                }
                if( !allNeededFields.contains( field.getName() ) ) {
                    continue;
                }
                fields.add( new NamedStorageType( className, field, types ) );
            }

            // calculate the vtable (the function indexes of the virtual methods)
            for( MethodInfo method : classFile.getMethods() ) {
                if( method.isStatic() || CONSTRUCTOR.equals( method.getName() ) ) {
                    continue;
                }
                FunctionName funcName = new FunctionName( method );

                addOrUpdateVTable( functions, funcName, false );
            }

            // search if there is a default implementation in an interface
            FunctionName funcName;
            String interName;
            ClassFile interClassFile;
            for( ConstantClass interClass : classFile.getInterfaces() ) {
                interName = interClass.getName();
                interClassFile = classFileLoader.get( interName );
                if (null != interClassFile) {
                    for( MethodInfo interMethod : interClassFile.getMethods() ) {
                        funcName = new FunctionName( interMethod );
                        if( functions.isUsed( funcName ) ) {
                            addOrUpdateVTable( functions, funcName, true );
                        }
                    }
                }
            }
        }

        /**
         * Add the function to the vtable or replace if already exists
         * 
         * @param functions
         *            the function manager
         * @param funcName
         *            the function to added
         * @param isDefault
         *            true, if the function is a default implementation of a interface
         */
        private void addOrUpdateVTable( FunctionManager functions, FunctionName funcName, boolean isDefault ) {
            int idx = 0;
            // search if the method is already in our list
            FunctionName func;
            for( ; idx < vtable.size(); idx++ ) {
                func = vtable.get( idx );
                if( func.methodName.equals( funcName.methodName ) && func.signature.equals( funcName.signature ) ) {
                    if( !isDefault || functions.getITableIndex( func ) >= 0 ) {
                        vtable.set( idx, funcName ); // use the override method
                        functions.markAsNeeded( funcName, true ); // mark all overridden methods also as needed if the super method is used
                    }
                    break;
                }
            }
            if( idx == vtable.size() && functions.isUsed( funcName ) ) {
                // if a new needed method then add it
                vtable.add( funcName );
            }
            if( idx < vtable.size() ) {
                functions.setVTableIndex( funcName, idx + VTABLE_FIRST_FUNCTION_INDEX );
            }
        }

        /**
         * List all interfaces of this StructType and and mark all instance methods of used interface methods.
         * 
         * <li>Add all used interfaces to the instanceOf set.</li>
         * <li>Create the itable for every interface. A list of real functions that should be called if the interface
         * method is called for this type.</li>
         * <li>mark all implementations of used interface method in this type as used. For example if
         * "java/util/List.size()I" is used anywhere and this StructType implements "java/util/List" then the "size()I"
         * method of this StrucType must also compiled.</li>
         * 
         * @param functions
         *            the used functions for the vtables of the types
         * @param types
         *            for types of fields
         * @param classFileLoader
         *            for loading the class files
         * @throws IOException
         *             if any I/O error occur on loading or writing
         */
        private void listInterfaces( FunctionManager functions, TypeManager types, ClassFileLoader classFileLoader ) throws IOException {
            // all implemented interfaces in the hierarchy
            Set<StructType> interfaceTypes = new LinkedHashSet<>();
            // all classes in the hierarchy
            ArrayList<ClassFile> classFiles = new ArrayList<>();

            // TODO: this is sketchy and probably should be rewritten...
            // list classes of the hierarchy and its interfaces
            Set<String> interfaceNames = new LinkedHashSet<>();
            ConstantClass superClass;
            for( ClassFile classFile = classFileLoader.get( name );; ) {
                if (null!=classFile) {
                    classFiles.add( classFile );
                    listInterfaceTypes( classFile, types, classFileLoader, interfaceTypes, interfaceNames );

                    superClass = classFile.getSuperClass();
                    if( superClass == null ) {
                        break;
                    }
                    classFile = classFileLoader.get( superClass.getName() );
                }
            }

            // if the top most class abstract then there can be no instance. A itable we need only for an instance
            if( classFiles.get( 0 ).isAbstract() ) {
                return;
            }

            // create the itables for all interfaces of this type
            String interName;
            ClassFile interClassFile;
            List<FunctionName> iMethods;
            FunctionName iName;
            MethodInfo method;
            ClassFile iClassFile;
            FunctionName methodName;
            for( StructType type : interfaceTypes ) {
                interName = type.name;
                interClassFile = classFileLoader.get( interName );
                iMethods = null;
                if (null!=interClassFile) {
                    for( MethodInfo interMethod : interClassFile.getMethods() ) {
                        iName = new FunctionName( interMethod );
                        if( functions.isUsed( iName ) ) {
                            method = null;
                            for( ClassFile classFile : classFiles ) {
                                method = classFile.getMethod( iName.methodName, iName.signature );
                                if( method != null ) {
                                    break;
                                }
                            }

                            if( method == null ) {
                                // search if there is a default implementation in an interface
                                for( String iClassName : interfaceNames ) {
                                    iClassFile = classFileLoader.get( iClassName );
                                    if (null!=iClassFile) {
                                        method = iClassFile.getMethod( iName.methodName, iName.signature );
                                        if( method != null ) {
                                            break;
                                        }
                                    }
                                }
                            }

                            if( method != null ) {
                                methodName = new FunctionName( method );
                                functions.markAsNeeded( methodName, !method.isStatic() );
                                if( iMethods == null ) {
                                    interfaceMethods.put( type, iMethods = new ArrayList<>() );
                                }
                                iMethods.add( methodName );
                                functions.setITableIndex( iName, iMethods.size() + 1 ); // on the first two place the classIndex and the next position is saved
                            } else {
                                throw new WasmException( String.format("No implementation of used interface method %s for type %s", iName.signatureName, name), -1 );
                            }
                        }
                    }
                }
            }
        }

        /**
         * List all interface StrucTypes recursively.
         * 
         * @param classFile
         *            The class from which the interfaces should listed
         * @param types
         *            the type manager with references to the types
         * @param classFileLoader
         *            for loading the class files
         * @param interfaceTypes
         *            the target
         * @param interfaceNames
         *            already listed interfaces to prevent a endless loop
         * @throws IOException
         *             if any I/O error occur on loading or writing
         */
        private void listInterfaceTypes( ClassFile classFile, TypeManager types, ClassFileLoader classFileLoader, Set<StructType> interfaceTypes, Set<String> interfaceNames ) throws IOException {
            // first list the direct interfaces
            ArrayList<ClassFile> later = null;
            String interName;
            ClassFile interClassFile;
            StructType type;
            for( ConstantClass interClass : classFile.getInterfaces() ) {
                interName = interClass.getName();
                if( interfaceNames.add( interName ) ) {
                    type = types.structTypes.get( interName );
                    if( type != null ) {
                        interfaceTypes.add( type );
                        // add all used interfaces to the instanceof set
                        instanceOFs.add( type );
                    }
                    interClassFile = classFileLoader.get( interName );
                    if( interClassFile != null ) {
                        if( later == null ) {
                            later = new ArrayList<>();
                        }
                        later.add( interClassFile );
                    }
                }
            }
            // then possible super interfaces, the order is important for default methods
            if( later != null ) {
                for( ClassFile interClassFile1 : later ) {
                    listInterfaceTypes( interClassFile1, types, classFileLoader, interfaceTypes, interfaceNames );
                }
            }
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public int getCode() {
            return code;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean isRefType() {
            return true;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean isSubTypeOf( AnyType type ) {
            if( type == this || type == ValueType.externref || type == ValueType.anyref || type == ValueType.eqref ) {
                return true;
            }
            if( !(type instanceof StructType) ) {
                return false;
            }
            StructType structType = (StructType)type;
            if( kind != structType.kind ) {
                return false;
            }

            try {
                ConstantClass superClass;
                String superName;
                ClassFile classFile = manager.classFileLoader.get( name );
                String otherTypeName = structType.name;
                while( classFile != null ) {
                    if( isSubTypeOf( classFile, otherTypeName )) {
                        return true;
                    }
                    superClass = classFile.getSuperClass();
                    if( superClass == null ) {
                        break;
                    }
                    superName = superClass.getName();
                    if( superName.equals( otherTypeName ) ) {
                        return true;
                    }
                    classFile = manager.classFileLoader.get( superName );
                }
            } catch( IOException ex ) {
                throw new UncheckedIOException( ex );
            }
            return false;
        }

        /**
         * Check for sub interface recursively.
         * 
         * @param classFile
         *            the class file to check
         * @param otherTypeName
         *            the searching interface name
         * @return true, if a sub interface
         * @throws IOException
         *             If any I/O error occur
         */
        private boolean isSubTypeOf( ClassFile classFile, String otherTypeName ) throws IOException {
            for( ConstantClass iface : classFile.getInterfaces() ) {
                if( iface.getName().equals( otherTypeName ) ) {
                    return true;
                }
                ClassFile iClassFile = manager.classFileLoader.get( iface.getName() );
                if( iClassFile != null && isSubTypeOf( iClassFile, otherTypeName ) ) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Get kind of the StructType
         * 
         * @return the type kind
         */
        public StructTypeKind getKind() {
            return kind;
        }

        /**
         * Get the name of the Java type
         * 
         * @return the name
         */
        public String getName() {
            return name;
        }

        /**
         * The running index of the class/type for class meta data, instanceof and interface calls.
         * 
         * @return the unique index
         */
        public int getClassIndex() {
            return classIndex;
        }

        /**
         * The running index of the component/array class/type for class meta data, instanceof and interface calls.
         * 
         * @return the unique index or -1 id not an array
         */
        protected int getComponentClassIndex() {
            return -1;
        }

        /**
         * Get the fields of this struct
         * 
         * @return the fields
         */
        public List<NamedStorageType> getFields() {
            return fields;
        }

        /**
         * Write the struct/class meta data to the datastream and set the offset position.
         * 
         * @param dataStream
         *            the target stream
         * @param getFunctionsID
         *            source for function IDs
         * @param options
         *            the compiler options
         * @throws IOException
         *             should never occur
         * @see TypeManager#TYPE_DESCRIPTION_INTERFACE_OFFSET
         * @see TypeManager#TYPE_DESCRIPTION_INSTANCEOF_OFFSET
         * @see TypeManager#TYPE_DESCRIPTION_TYPE_NAME
         */
        public void writeToStream( ByteArrayOutputStream dataStream, ToIntFunction<FunctionName> getFunctionsID, WasmOptions options ) throws IOException {
            /*
                 ┌───────────────────────────────────────┐
                 | Offset to the interfaces    [4 bytes] |
                 ├───────────────────────────────────────┤
                 | Offset to the instanceof    [4 bytes] |
                 ├───────────────────────────────────────┤
                 | String id of the class name [4 bytes] |
                 ├───────────────────────────────────────┤
                 | array component type        [4 bytes] |
                 ├───────────────────────────────────────┤
                 | Offset to field descript.   [4 bytes] |
                 ├───────────────────────────────────────┤
                 | first vtable entry          [4 bytes] |
                 ├───────────────────────────────────────┤
                 |     .....                             |
                 ├───────────────────────────────────────┤
                 | interface calls (itable)              |
                 ├───────────────────────────────────────┤
                 | list of instanceof    [4*(n+1) bytes] |
                 ├───────────────────────────────────────┤
                 |     count of entries        [4 bytes] |
                 ├───────────────────────────────────────┤
                 |     own class id            [4 bytes] |
                 ├───────────────────────────────────────┤
                 |     .....             [4*(n-1) bytes] |
                 └───────────────────────────────────────┘
             */
            this.vtableOffset = dataStream.size();

            LittleEndianOutputStream header = new LittleEndianOutputStream( dataStream );
            LittleEndianOutputStream data = new LittleEndianOutputStream();
            int functIdx; // maybe initialize and reinitialize in the next section
            for( FunctionName funcName : vtable ) {
                functIdx = getFunctionsID.applyAsInt( funcName );
                data.writeInt32( functIdx );
            }

            // header position TYPE_DESCRIPTION_INTERFACE_OFFSET
            header.writeInt32( data.size() + VTABLE_FIRST_FUNCTION_INDEX * 4 ); // offset of interface calls
            List<FunctionName> iMethods;
            int nextClassPosition;
            for( Entry<StructType, List<FunctionName>> entry : interfaceMethods.entrySet() ) {
                data.writeInt32( entry.getKey().getClassIndex() );
                iMethods = entry.getValue();
                nextClassPosition = 4 * (2 + iMethods.size());
                data.writeInt32( nextClassPosition );
                for( FunctionName funcName : iMethods ) {
                    functIdx = getFunctionsID.applyAsInt( funcName );
                    data.writeInt32( functIdx );
                }
            }
            data.writeInt32( 0 ); // no more interface in itable

            // header position TYPE_DESCRIPTION_INSTANCEOF_OFFSET
            header.writeInt32( data.size() + VTABLE_FIRST_FUNCTION_INDEX * 4 ); // offset of instanceeof list
            data.writeInt32( instanceOFs.size() );
            for( StructType type : instanceOFs ) {
                data.writeInt32( type.getClassIndex() );
            }

            int nameIdx = options.strings.get( getName().replace( '/', '.' ) );
            // header position TYPE_DESCRIPTION_TYPE_NAME
            header.writeInt32( nameIdx ); // string id of the className

            // header position TYPE_DESCRIPTION_ARRAY_TYPE
            header.writeInt32( getComponentClassIndex() );

            // header position TYPE_DESCRIPTION_FIELDS_OFFSET
            header.writeInt32( data.size() + VTABLE_FIRST_FUNCTION_INDEX * 4 );
            if( kind == StructTypeKind.normal ) {
                for( NamedStorageType field : fields ) {
                    nameIdx = options.strings.get( field.getName() );
                    //TODO adapt this format for the reflection API
                    data.writeInt32( nameIdx );
                    data.writeInt32( field.getType().getCode() );
                }
            }

            data.writeTo( dataStream );
        }

        /**
         * Get the vtable offset.
         * 
         * @return the offset
         */
        public int getVTable() {
            return this.vtableOffset;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            return String.format("$%s", name);
        }
    }

    /**
     * A generated type that represent a lambda expression
     */
    class LambdaType extends StructType {

        private ArrayList<NamedStorageType> paramFields;

        private StructType                  interfaceType;

        private final FunctionName                methodName;

        private String                      interfaceMethodName;

        /**
         * Create a lambda type
         * 
         * @param name
         *            the Lambda Java class name
         * @param method
         *            the name BootstrapMethod from the parsed class file
         * @param params
         *            the parameters of the constructor and type fields
         * @param interfaceType
         *            the implemented interface type
         * @param syntheticLambdaFunctionName
         *            the real method in the parent class that implements the lambda expression
         * @param interfaceMethodName
         *            the name of the implemented method in the interface
         * @param manager
         *            the manager which hold all StructTypes
         * @param lineNumber
         *            the line number in the Java source code
         */
        LambdaType( @Nonnull String name, @Nonnull BootstrapMethod method, ArrayList<AnyType> params, StructType interfaceType, FunctionName syntheticLambdaFunctionName, String interfaceMethodName, @Nonnull TypeManager manager, int lineNumber ) {
            super( name, StructTypeKind.lambda, manager );
            this.paramFields = new ArrayList<>( params.size() );
            for( int i = 0; i < params.size(); i++ ) {
                paramFields.add( new NamedStorageType( params.get( i ), EMPTY_STRING, String.format("arg$%d", (i + 1)) ) );
            }
            this.interfaceType = interfaceType;
            this.interfaceMethodName = interfaceMethodName;

            methodName = new SyntheticFunctionName( name, interfaceMethodName, method.getSamMethodType() ) {
                @Override
                protected boolean hasWasmCode() {
                    return true;
                }

                @Override
                protected boolean istStatic() {
                    return false;
                }

                @Override
                protected WasmCodeBuilder getCodeBuilder( WatParser watParser ) {
                    WasmCodeBuilder codebuilder = watParser;
                    ArrayList<AnyType> sig = new ArrayList<>();
                    sig.add( LambdaType.this );
                    for( Iterator<AnyType> it = getSignature( manager ); it.hasNext(); ) {
                        sig.add( it.next() );
                    }
                    watParser.reset( null, null, sig.iterator() );

                    // first add the values from the Lambda constructor which is saved in the synthetic class
                    for( int i = 0; i < paramFields.size(); i++ ) {
                        codebuilder.addLoadStoreInstruction( LambdaType.this, true, 0, 0, -1 );
                        codebuilder.addStructInstruction( StructOperator.GET, name, paramFields.get( i ), 0, lineNumber );
                    }

                    // forward the parameter from the current call without the THIS parameter because the call lambda method is static
                    AnyType anyType;
                    for( int i = 1; i < sig.size(); i++ ) {
                        anyType = sig.get( i );
                        if( anyType == null ) {
                            break;
                        }
                        codebuilder.addLoadStoreInstruction( anyType, true, i, 0, lineNumber );
                    }

                    boolean needThisParameter = false;
                    try {
                        // a lambda expression function is mostly static else it need access to field.
                        ClassFile classFile = classFileLoader.get( syntheticLambdaFunctionName.className );
                        if (null != classFile) {
                            MethodInfo methodInfo = classFile.getMethod( syntheticLambdaFunctionName.methodName, syntheticLambdaFunctionName.signature );
                            needThisParameter = !methodInfo.isStatic();
                        }
                    } catch( IOException ex ) {
                        throw WasmException.create( ex, null, syntheticLambdaFunctionName.className, syntheticLambdaFunctionName.methodName, lineNumber );
                    }

                    codebuilder.addCallInstruction( syntheticLambdaFunctionName, needThisParameter, 0, lineNumber );
                    return watParser;
                }
            };
        }

        /**
         * The parameters of the constructor
         * 
         * @return the parameters
         */
        ArrayList<NamedStorageType> getParamFields() {
            return paramFields;
        }

        /**
         * The implemented interface type
         * 
         * @return the interface type
         */
        StructType getInterfaceType() {
            return interfaceType;
        }

        /**
         * The real method in the parent class that implements the lambda expression
         * 
         * @return the function name
         */
        @Nonnull
        FunctionName getLambdaMethod() {
            return methodName;
        }

        /**
         * The name of the implemented method in the interface
         * 
         * @return the name
         */
        String getInterfaceMethodName() {
            return interfaceMethodName;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean isSubTypeOf( AnyType type ) {
            if( type == this || type == ValueType.externref || type == ValueType.anyref || type == ValueType.eqref ) {
                return true;
            }
            return type == interfaceType;
        }
    }

    /**
     * A type that can use for a block
     */
    public static class BlockType implements AnyType {

        @Nonnull
        private final List<AnyType> params;

        @Nonnull
        private final List<AnyType> results;

        private int                 code;

        private String              name;

        public BlockType( List<AnyType> params, List<AnyType> results ) {
            this.params = params;
            this.results = results;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public int getCode() {
            return code;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean isRefType() {
            return false;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean isSubTypeOf( AnyType type ) {
            return type == this;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public int hashCode() {
            return params.hashCode() + results.hashCode();
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean equals( Object obj ) {
            if( this == obj ) {
                return true;
            }
            if( obj == null ) {
                return false;
            }
            if( getClass() != obj.getClass() ) {
                return false;
            }
            BlockType other = (BlockType)obj;
            return params.equals( other.params ) && results.equals( other.results );
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            if( name != null ) {
                return name;
            }
            return super.toString();
        }

        public List<AnyType> getParams() {
            return params;
        }

        public List<AnyType> getResults() {
            return results;
        }

        public void setName( String name ) {
            this.name = name;
        }
    }

}
