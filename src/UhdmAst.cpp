#include <vector>
#include <stack>
#include <functional>
#include <algorithm>
#include <regex>

#include <uhdm/uhdm.h>

#include "V3Ast.h"
#include "V3ParseSym.h"
#include "V3Global.h"
#include "UhdmAst.h"

namespace UhdmAst {

// Walks through one-to-many relationships from given parent
// node through the VPI interface, visiting child nodes belonging to
// ChildrenNodeTypes that are present in the given object.
void visit_one_to_many(const std::vector<int> childrenNodeTypes, vpiHandle parentHandle,
                       UhdmShared& shared, const std::function<void(AstNode*)>& f) {
    for (auto child : childrenNodeTypes) {
        vpiHandle itr = vpi_iterate(child, parentHandle);
        while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
            auto* childNode = visit_object(vpi_child_obj, shared);
            f(childNode);
            vpi_release_handle(vpi_child_obj);
        }
        vpi_release_handle(itr);
    }
}

// Walks through one-to-one relationships from given parent
// node through the VPI interface, visiting child nodes belonging to
// ChildrenNodeTypes that are present in the given object.
void visit_one_to_one(const std::vector<int> childrenNodeTypes, vpiHandle parentHandle,
                      UhdmShared& shared, const std::function<void(AstNode*)>& f) {
    for (auto child : childrenNodeTypes) {
        vpiHandle itr = vpi_handle(child, parentHandle);
        if (itr) {
            auto* childNode = visit_object(itr, shared);
            f(childNode);
        }
        vpi_release_handle(itr);
    }
}

void sanitize_str(std::string& s) {
    if (!s.empty()) {
        auto pos = s.rfind("@");
        s = s.substr(pos + 1);
        // Replace [ and ], seen in GenScope names
        s = std::regex_replace(s, std::regex("\\["), "__BRA__");
        s = std::regex_replace(s, std::regex("\\]"), "__KET__");
    }
}

std::string remove_last_sanitized_index(const std::string& s) {
    if (s.size() > 7 && s.substr(s.size() - 7) == "__KET__") {
        auto pos = s.rfind("__BRA__");
        return s.substr(0, pos);
    }
    return s;
}

FileLine* make_fileline(vpiHandle obj_h) {
    std::string filename = "uhdm";
    if (auto* s = vpi_get_str(vpiFile, obj_h)) { filename = s; }
    const int lineNo = vpi_get(vpiLineNo, obj_h);
    const int endLineNo = vpi_get(vpiEndLineNo, obj_h);
    const int columnNo = vpi_get(vpiColumnNo, obj_h);
    const int endColumnNo = vpi_get(vpiEndColumnNo, obj_h);
    auto* fl = new FileLine(filename);
    fl->firstLineno(lineNo);
    fl->lastLineno(endLineNo);
    fl->firstColumn(columnNo);
    fl->lastColumn(endColumnNo);
    return fl;
}

std::string get_object_name(vpiHandle obj_h, const std::vector<int>& name_fields = {vpiName}) {
    std::string objectName;
    for (auto name : name_fields) {
        if (auto s = vpi_get_str(name, obj_h)) {
            objectName = s;
            sanitize_str(objectName);
            break;
        }
    }
    return objectName;
}

bool is_imported(vpiHandle obj_h) {
    if (auto s = vpi_get_str(vpiImported, obj_h)) {
        return true;
    } else {
        return false;
    }
}

void remove_scope(std::string& s) {
    auto pos = s.rfind("::");
    if (pos != std::string::npos) s = s.substr(pos + 2);
}

AstParseRef* getVarRefIfAlreadyDeclared(vpiHandle obj_h, UhdmShared& shared) {
    std::string objectName = get_object_name(obj_h);
    const uhdm_handle* const handle = (const uhdm_handle*)obj_h;
    const UHDM::BaseClass* const object = (const UHDM::BaseClass*)handle->object;
    if (shared.visited_objects.find(object) != shared.visited_objects.end()) {
        // Already seen this, create reference
        return new AstParseRef(make_fileline(obj_h), VParseRefExp::en::PX_TEXT, objectName,
                               nullptr, nullptr);
    }
    shared.visited_objects.insert(object);
    return nullptr;
}

AstPackage* get_package(UhdmShared& shared, const std::string& objectName) {
    std::size_t delimiter_pos = objectName.rfind("::");
    std::size_t prefix_pos = objectName.find("::");
    AstPackage* classpackagep = nullptr;
    if (delimiter_pos != std::string::npos) {
        std::string classpackageName = "";
        if (prefix_pos < delimiter_pos) {
            // "Nested" packages - package importing package
            // Last one is where definition is located
            classpackageName = objectName.substr(prefix_pos + 2, delimiter_pos - prefix_pos - 2);
        } else {
            // Simple package reference
            classpackageName = objectName.substr(0, delimiter_pos);
        }
        // Nested or not, func is named after last package
        auto object_name = objectName.substr(delimiter_pos + 2, objectName.length());
        UINFO(7, "Found package prefix: " << classpackageName << std::endl);
        remove_scope(classpackageName);
        auto it = shared.package_map.find(classpackageName);
        if (it != shared.package_map.end()) { classpackagep = it->second; }
    }
    return classpackagep;
}

bool is_expr_context(vpiHandle obj_h) {
    auto parent_h = vpi_handle(vpiParent, obj_h);
    if (parent_h) {
        auto parent_type = vpi_get(vpiType, parent_h);
        switch (parent_type) {
        case vpiOperation:
        case vpiIf:
        case vpiIfElse:
        case vpiAssignStmt:
        case vpiAssignment:
        case vpiContAssign:
        case vpiReturn: {
            return true;
        }
        case vpiBegin:
        case vpiFuncCall:
        case vpiTaskCall:
        case vpiCaseItem: {
            return false;
        }
        default: {
            UINFO(3, "Encountered unhandled parent type in " << __FUNCTION__ << std::endl);
            return false;
        }
        }
    } else {
        UINFO(3, "Missing parent handle in " << __FUNCTION__ << std::endl);
        // TODO: it seems that this happens only in expr context?
        return true;
    }
}

string deQuote(FileLine* fileline, string text) {
    // Fix up the quoted strings the user put in, for example "\"" becomes "
    // Reverse is V3OutFormatter::quoteNameControls(...)
    bool quoted = false;
    string newtext;
    unsigned char octal_val = 0;
    int octal_digits = 0;
    for (string::const_iterator cp = text.begin(); cp != text.end(); ++cp) {
        if (quoted) {
            if (isdigit(*cp)) {
                octal_val = octal_val * 8 + (*cp - '0');
                if (++octal_digits == 3) {
                    octal_digits = 0;
                    quoted = false;
                    newtext += octal_val;
                }
            } else {
                if (octal_digits) {
                    // Spec allows 1-3 digits
                    octal_digits = 0;
                    quoted = false;
                    newtext += octal_val;
                    --cp;  // Backup to reprocess terminating character as non-escaped
                    continue;
                }
                quoted = false;
                if (*cp == 'n')
                    newtext += '\n';
                else if (*cp == 'a')
                    newtext += '\a';  // SystemVerilog 3.1
                else if (*cp == 'f')
                    newtext += '\f';  // SystemVerilog 3.1
                else if (*cp == 'r')
                    newtext += '\r';
                else if (*cp == 't')
                    newtext += '\t';
                else if (*cp == 'v')
                    newtext += '\v';  // SystemVerilog 3.1
                else if (*cp == 'x' && isxdigit(cp[1]) && isxdigit(cp[2])) {  // SystemVerilog 3.1
#define vl_decodexdigit(c) ((isdigit(c) ? ((c) - '0') : (tolower((c)) - 'a' + 10)))
                    newtext += (char)(16 * vl_decodexdigit(cp[1]) + vl_decodexdigit(cp[2]));
                    cp += 2;
                } else if (isalnum(*cp)) {
                    fileline->v3error("Unknown escape sequence: \\" << *cp);
                    break;
                } else
                    newtext += *cp;
            }
        } else if (*cp == '\\') {
            quoted = true;
            octal_digits = 0;
        } else if (*cp != '"') {
            newtext += *cp;
        }
    }
    return newtext;
}

AstNodeDType* applyPackedRanges(FileLine* fl, vpiHandle obj_h, AstNodeDType* dtypep,
                                UhdmShared& shared) {
    std::stack<AstRange*> range_stack;
    visit_one_to_many({vpiRange}, obj_h, shared, [&](AstNode* nodep) {
        AstRange* rangeNodep = reinterpret_cast<AstRange*>(nodep);
        range_stack.push(rangeNodep);
    });

    AstBasicDType* basicp = VN_CAST(dtypep, BasicDType);
    if (basicp && !basicp->rangep() && !range_stack.empty()) {
        basicp->rangep(range_stack.top());
        range_stack.pop();
        dtypep = basicp;
    }
    while (!range_stack.empty()) {
        dtypep = new AstPackArrayDType(fl, VFlagChildDType(), dtypep, range_stack.top());
        range_stack.pop();
    }
    return dtypep;
}

AstNodeDType* applyUnpackedRanges(FileLine* fl, vpiHandle obj_h, AstNodeDType* dtypep,
                                  UhdmShared& shared) {
    std::stack<AstRange*> range_stack;
    visit_one_to_many({vpiRange}, obj_h, shared, [&](AstNode* nodep) {
        AstRange* rangeNodep = reinterpret_cast<AstRange*>(nodep);
        range_stack.push(rangeNodep);
    });

    while (!range_stack.empty()) {
        dtypep = new AstUnpackArrayDType(fl, VFlagChildDType(), dtypep, range_stack.top());
        range_stack.pop();
    }
    return dtypep;
}

AstNode* get_class_package_ref_node(FileLine* fl, std::string objectName, UhdmShared& shared) {
    AstNode* refp = nullptr;
    size_t colon_pos = objectName.find("::");
    while (colon_pos != std::string::npos) {
        std::string classPkgName = objectName.substr(0, colon_pos);
        objectName = objectName.substr(colon_pos + 2, objectName.length());

        UINFO(7, "Creating ClassOrPackageRef" << std::endl);
        AstPackage* classpackagep = nullptr;
        auto it = shared.package_map.find(classPkgName);
        if (it != shared.package_map.end()) { classpackagep = it->second; }
        AstNode* classpackageref
            = new AstClassOrPackageRef(fl, classPkgName, classpackagep, nullptr);
        shared.m_symp->nextId(classpackagep);
        if (refp == nullptr)
            refp = classpackageref;
        else
            refp = new AstDot(fl, true, refp, classpackageref);

        colon_pos = objectName.find("::");
    }
    return refp;
}

AstNode* get_referenceNode(FileLine* fl, string name, UhdmShared& shared) {
    AstNode* colon_refp = get_class_package_ref_node(fl, name, shared);
    size_t colon_pos = name.rfind("::");
    if (colon_pos != std::string::npos) name = name.substr(colon_pos + 2);

    AstNode* dot_refp = nullptr;

    size_t dot_pos = name.find('.');
    if (dot_pos != std::string::npos) {
        std::string lhs = name.substr(0, dot_pos);
        std::string rhs = name.substr(dot_pos + 1, name.length());
        AstParseRef* lhsNode
            = new AstParseRef(fl, VParseRefExp::en::PX_TEXT, lhs, nullptr, nullptr);
        AstNode* rhsNode = get_referenceNode(fl, rhs, shared);
        dot_refp = new AstDot(fl, false, lhsNode, rhsNode);
    } else {
        dot_refp = new AstParseRef(fl, VParseRefExp::en::PX_TEXT, name, nullptr, nullptr);
    }
    return AstDot::newIfPkg(fl, colon_refp, dot_refp);
}

AstNode* get_value_as_node(vpiHandle obj_h, bool need_decompile = false) {
    AstNode* valueNodep = nullptr;
    std::string valStr;

    // Most nodes will have raw value in vpiDecompile, leave deducing the type to Verilator
    if (need_decompile) {
        if (auto s = vpi_get_str(vpiDecompile, obj_h)) {
            valStr = s;
            auto type = vpi_get(vpiConstType, obj_h);
            if (type == vpiStringConst) {
                valueNodep = new AstConst(make_fileline(obj_h), AstConst::VerilogStringLiteral(),
                                          deQuote(make_fileline(obj_h), valStr));
            } else if (type == vpiRealConst) {
                bool parseSuccess;
                double value = VString::parseDouble(valStr, &parseSuccess);
                UASSERT(parseSuccess, "Unable to parse real value: " + valStr);

                valueNodep = new AstConst(make_fileline(obj_h), AstConst::RealDouble(), value);
            } else {
                valStr = s;
                if (valStr.find('\'') == std::string::npos) {
                    if (vpi_get(vpiSize, obj_h) == -1) {
                        std::string actualValStr;
                        if (valStr == "0")
                            actualValStr = "'0";
                        else if (valStr == "1" || valStr == "18446744073709551615")
                            // Surelog's default constant size is 64
                            // 18446744073709551615 is 2^64 - 1
                            actualValStr = "'1";
                        else if (valStr == "x" || valStr == "X")
                            actualValStr = "'X";
                        else if (valStr == "z" || valStr == "Z")
                            actualValStr = "'Z";
                        else
                            v3error("Unexpected value with vpiSize: -1");

                        return new AstConst(make_fileline(obj_h), AstConst::StringToParse(), actualValStr.c_str());
                    }

                    if (int size = vpi_get(vpiSize, obj_h)) {
                        if (type == vpiBinaryConst) valStr = "'b" + valStr;
                        else if (type == vpiOctConst) valStr = "'o" + valStr;
                        else if (type == vpiHexConst) valStr = "'h" + valStr;
                        else valStr = "'d" + valStr;
                        valStr = std::to_string(size) + valStr;
                    }
                    auto* constp = new AstConst(make_fileline(obj_h), AstConst::StringToParse(), valStr.c_str());
                    auto& num = constp->num();
                    if (num.width() >= 32 && num.widthMin() <= 32) {
                        num.width(32, false);
                        num.isSigned(true);
                        constp = new AstConst(make_fileline(obj_h), num);
                    }
                    valueNodep = constp;
                } else {
                    auto* constp = new AstConst(make_fileline(obj_h), AstConst::StringToParse(), valStr.c_str());
                    valueNodep = constp;
                }
            }
            return valueNodep;
        }
    } else {
        UINFO(7, "Requested vpiDecompile value not found in UHDM" << std::endl);
    }
    s_vpi_value val;
    vpi_get_value(obj_h, &val);
    switch (val.format) {
    case vpiIntVal:
    case vpiScalarVal:
    case vpiUIntVal: {
        if (val.format == vpiIntVal)
            valStr = std::to_string(val.value.integer);
        else if (val.format == vpiScalarVal)
            valStr = std::to_string(val.value.scalar);
        else if (val.format == vpiUIntVal)
            valStr = std::to_string(val.value.uint);

        if (valStr[0] == '-') {
            valStr = valStr.substr(1);
            auto* inner = new AstConst(make_fileline(obj_h), AstConst::StringToParse(), valStr.c_str());
            valueNodep = new AstNegate(make_fileline(obj_h), inner);
            break;
        }

        if (int size = vpi_get(vpiSize, obj_h))
            valStr = std::to_string(size) + "'d" + valStr;
        auto* constp = new AstConst(make_fileline(obj_h), AstConst::StringToParse(), valStr.c_str());
        auto& num = constp->num();
        if (num.width() >= 32 && num.widthMin() <= 32) {
            num.width(32, false);
            num.isSigned(true);
            constp = new AstConst(make_fileline(obj_h), num);
        }
        valueNodep = constp;
        break;
    }
    case vpiRealVal: {
        valStr = std::to_string(val.value.real);

        bool parseSuccess;
        double value = VString::parseDouble(valStr, &parseSuccess);
        UASSERT(parseSuccess, "Unable to parse real value: " + valStr);

        valueNodep = new AstConst(make_fileline(obj_h), AstConst::RealDouble(), value);
        break;
    }
    case vpiBinStrVal:
    case vpiOctStrVal:
    case vpiDecStrVal:
    case vpiHexStrVal: {
        // if vpiDecompile is unavailable i.e. in EnumConst, cast the string
        if (val.format == vpiBinStrVal)
            valStr = "'b" + std::string(val.value.str);
        else if (val.format == vpiOctStrVal)
            valStr = "'o" + std::string(val.value.str);
        else if (val.format == vpiDecStrVal)
            valStr = "'d" + std::string(val.value.str);
        else if (val.format == vpiHexStrVal)
            valStr = "'h" + std::string(val.value.str);
        if (int size = vpi_get(vpiSize, obj_h))
            valStr = std::to_string(size) + valStr;
        auto* constp = new AstConst(make_fileline(obj_h), AstConst::StringToParse(), valStr.c_str());
        valueNodep = constp;
        break;
    }
    case vpiStringVal: {
        if (auto* s = val.value.str) valStr = std::to_string(*s);
        valStr.assign(val.value.str);
        valueNodep = new AstConst(make_fileline(obj_h), AstConst::VerilogStringLiteral(),
                                  deQuote(make_fileline(obj_h), valStr));
        break;
    }
    case 0: {
        UINFO(7, "No value; value format is 0" << std::endl);
        return nullptr;
    }
    default: {
        v3error("Encountered unknown value format " << val.format << std::endl);
        break;
    }
    }
    return valueNodep;
}

AstRefDType* get_type_reference(FileLine* fl, std::string objectName, std::string fullTypeName,
                                UhdmShared& shared) {
    AstRefDType* refp = nullptr;
    size_t delimiter_pos = fullTypeName.rfind("::");
    size_t prefix_pos = fullTypeName.find("::");
    if (delimiter_pos == string::npos) {
        UINFO(7, "No package prefix found, creating ref" << std::endl);
        refp = new AstRefDType(fl, fullTypeName);
    } else {
        std::string classpackageName = "";
        if (prefix_pos < delimiter_pos) {
            // "Nested" packages - package importing package
            // Last one is where definition is located
            classpackageName = fullTypeName.substr(prefix_pos + 2, delimiter_pos - prefix_pos - 2);
        } else {
            // Simple package reference
            classpackageName = fullTypeName.substr(0, delimiter_pos);
        }

        UINFO(7, "Found package prefix: " << classpackageName << std::endl);
        // If we are in the same package - do not create reference,
        // as it will confuse Verilator
        if (classpackageName
            == shared.package_prefix.substr(0, shared.package_prefix.length() - 2)) {
            UINFO(7, "In the same package, creating simple ref" << std::endl);
            refp = new AstRefDType(fl, objectName);
        } else {
            UINFO(7, "Creating ClassOrPackageRef" << std::endl);
            AstPackage* classpackagep = nullptr;
            auto it = shared.package_map.find(classpackageName);
            if (it != shared.package_map.end()) { classpackagep = it->second; }
            AstNode* classpackageref
                = new AstClassOrPackageRef(fl, classpackageName, classpackagep, nullptr);
            shared.m_symp->nextId(classpackagep);
            refp = new AstRefDType(fl, objectName, classpackageref, nullptr);
        }
    }
    return refp;
}
AstBasicDTypeKwd get_kwd_for_type(int vpi_var_type) {
    switch (vpi_var_type) {
    case vpiLogicTypespec:
    case vpiLogicNet:
    case vpiLogicVar: {
        return AstBasicDTypeKwd::LOGIC;
    }
    case vpiIntTypespec:
    case vpiIntVar: {
        return AstBasicDTypeKwd::INT;
    }
    case vpiLongIntTypespec:
    case vpiLongIntVar: {
        return AstBasicDTypeKwd::LONGINT;
    }
    case vpiIntegerTypespec:
    case vpiIntegerNet:
    case vpiIntegerVar: {
        return AstBasicDTypeKwd::INTEGER;
    }
    case vpiShortIntTypespec:
    case vpiShortIntVar: {
        return AstBasicDTypeKwd::SHORTINT;
    }
    case vpiBitTypespec:
    case vpiBitVar: {
        return AstBasicDTypeKwd::BIT;
    }
    case vpiByteTypespec:
    case vpiByteVar: {
        return AstBasicDTypeKwd::BYTE;
    }
    case vpiShortRealTypespec:
    case vpiShortRealVar: {
        // Warning thrown by original verilator
        auto *fl = new FileLine("uhdm");
        fl->v3warn(SHORTREAL,
                   "Unsupported: shortreal being promoted to real (suggest use real instead)");
        return AstBasicDTypeKwd::DOUBLE;
    }
    case vpiRealTypespec:
    case vpiRealVar: {
        return AstBasicDTypeKwd::DOUBLE;
    }
    case vpiStringTypespec:
    case vpiStringVar: {
        return AstBasicDTypeKwd::STRING;
    }
    case vpiTimeTypespec:
    case vpiTimeNet:
    case vpiTimeVar: {
        return AstBasicDTypeKwd::TIME;
    }
    case vpiChandleTypespec:
    case vpiChandleVar: {
        return AstBasicDTypeKwd::CHANDLE;
    }
    case vpiEnumTypespec:
    case vpiEnumVar:
    case vpiEnumNet:
    case vpiStructTypespec:
    case vpiStructNet:
    case vpiStructVar:
    case vpiArrayTypespec:
    case vpiPackedArrayTypespec:
    case vpiUnionTypespec: {
        // Not a basic dtype, needs further handling
        return AstBasicDTypeKwd::UNKNOWN;
    }
    default: v3error("Unknown object type " << vpi_var_type);
    }
    return AstBasicDTypeKwd::UNKNOWN;
}

AstNodeDType* getDType(FileLine* fl, vpiHandle obj_h, UhdmShared& shared) {

    AstNodeDType* dtypep = nullptr;
    auto type = vpi_get(vpiType, obj_h);
    if (type == vpiPort) {
        auto ref_h = vpi_handle(vpiLowConn, obj_h);
        if (!ref_h) {
            v3error("Could not get lowconn handle for port, aborting");
            return nullptr;
        }
        auto actual_h = vpi_handle(vpiActual, ref_h);
        if (!actual_h) {
            v3error("Could not get actual handle for port, aborting");
            return nullptr;
        }
        auto ref_type = vpi_get(vpiType, actual_h);
        if (ref_type == vpiLogicNet || ref_type == vpiIntegerNet || ref_type == vpiTimeNet
            || ref_type == vpiArrayNet || ref_type == vpiPackedArrayNet) {
            type = ref_type;
            obj_h = actual_h;
        } else if (ref_type == vpiEnumNet || ref_type == vpiStructNet || ref_type == vpiStructVar
                   || ref_type == vpiEnumVar) {
            auto typespec_h = vpi_handle(vpiTypedef, obj_h);
            if (typespec_h) {
                type = vpi_get(vpiType, typespec_h);
                obj_h = typespec_h;
            }
        } else if (ref_type == vpiModport || ref_type == vpiInterface) {
            // Special handling, generate only reference
            vpiHandle iface_h = nullptr;
            if (ref_type == vpiModport) {
                iface_h = vpi_handle(vpiInterface, actual_h);
            } else if (ref_type == vpiInterface) {
                iface_h = actual_h;
            }
            std::string cellName, ifaceName;
            if (auto s = vpi_get_str(vpiName, ref_h)) {
                cellName = s;
                sanitize_str(cellName);
            }
            if (auto s = vpi_get_str(vpiDefName, iface_h)) {
                ifaceName = s;
                sanitize_str(ifaceName);
            }
            return new AstIfaceRefDType(fl, cellName, ifaceName);
        }
    }
    if (type == vpiEnumNet || type == vpiStructNet || type == vpiStructVar || type == vpiEnumVar) {
        auto typespec_h = vpi_handle(vpiTypespec, obj_h);
        if (typespec_h) {
            type = vpi_get(vpiType, typespec_h);
            obj_h = typespec_h;
        }
    }
    AstBasicDTypeKwd keyword = AstBasicDTypeKwd::UNKNOWN;
    switch (type) {
    case vpiLogicNet:
    case vpiLogicVar:
    case vpiBitVar: {
        if (auto typespec_h = vpi_handle(vpiTypespec, obj_h)) {
            dtypep = getDType(fl, typespec_h, shared);
            if (!dtypep)
                v3error("Unable to handle vpiTypespec node in logic net, logic var or bit var");
        } else {
            AstBasicDTypeKwd keyword = get_kwd_for_type(type);
            dtypep = new AstBasicDType(fl, keyword);
        }
        dtypep = applyPackedRanges(fl, obj_h, dtypep, shared);
        break;
    }
    case vpiLogicTypespec:
    case vpiBitTypespec:
    case vpiIntTypespec:
    case vpiLongIntTypespec:
    case vpiIntegerTypespec:
    case vpiShortIntTypespec:
    case vpiShortRealTypespec:
    case vpiByteTypespec:
    case vpiRealTypespec:
    case vpiStringTypespec:
    case vpiChandleTypespec:
    case vpiTimeTypespec:
    case vpiArrayTypespec:
    case vpiPackedArrayTypespec:
    case vpiStructTypespec:
    case vpiEnumTypespec:
    case vpiUnionTypespec: {
        if (vpiHandle alias_h = vpi_handle(vpiTypedefAlias, obj_h)) {
            return getDType(fl, alias_h, shared);
        }
        std::string typespec_name = get_object_name(obj_h);
        std::string full_type_name;
        if (typespec_name != "") {
            auto pos = typespec_name.rfind("::");
            if (pos != std::string::npos) typespec_name = typespec_name.substr(pos + 2);

            std::string package_name = "";
            if (vpiHandle instance_h = vpi_handle(vpiInstance, obj_h)) {
                if (vpi_get(vpiType, instance_h) == vpiPackage)
                    package_name = get_object_name(instance_h, {vpiDefName});
                vpi_release_handle(instance_h);
            }
            if (package_name != "")
                full_type_name = package_name + "::" + typespec_name;
            else
                full_type_name = typespec_name;
            dtypep = get_type_reference(fl, typespec_name, full_type_name, shared);
            break;
        } else {
            // Typespec without name, construct the type by process_typespec
            dtypep = VN_CAST(process_typespec(obj_h, shared), NodeDType);
            if (!dtypep) v3error("Unable to handle anonymous vpiTypespec node");
            break;
        }
    }
    case vpiIntegerNet:
    case vpiTimeNet:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiIntegerVar:
    case vpiShortIntVar:
    case vpiShortRealVar:
    case vpiByteVar:
    case vpiRealVar:
    case vpiStringVar:
    case vpiTimeVar:
    case vpiChandleVar: {
        AstBasicDTypeKwd keyword = get_kwd_for_type(type);
        dtypep = new AstBasicDType(fl, keyword);
        break;
    }
    case vpiEnumNet:
    case vpiStructNet:
    case vpiEnumVar:
    case vpiStructVar: {
        std::string type_string;
        const uhdm_handle* const handle = (const uhdm_handle*)obj_h;
        const UHDM::BaseClass* const object = (const UHDM::BaseClass*)handle->object;

        std::string type_name = get_object_name(obj_h);
        auto pos = type_name.rfind("::");
        if (pos != std::string::npos) type_name = type_name.substr(pos + 2);

        if (shared.visited_types_map.find(object) != shared.visited_types_map.end()) {
            type_string = shared.visited_types_map[object];
            dtypep = get_type_reference(fl, type_name, type_string, shared);
        } else {
            // Type not found or object pointer mismatch, but let's try to create a reference
            // to be resolved later
            // Simple reference only, prefix is not stored in name
            UINFO(7, "No match found, creating ref to name" << type_name << std::endl);
            dtypep = new AstRefDType(fl, type_name);
        }
        break;
    }
    case vpiPackedArrayNet:
    case vpiPackedArrayVar: {
        auto typespec_h = vpi_handle(vpiTypespec, obj_h);
        if (typespec_h == 0) {  // Try to get the type from one of the elements
            auto itr = vpi_iterate(vpiElement, obj_h);
            auto element_h = vpi_scan(itr);
            typespec_h = vpi_handle(vpiTypespec, element_h);
        }

        if (typespec_h) {
            dtypep = getDType(fl, typespec_h, shared);
        } else {
            v3error("Missing typespec for packed_array_var");
        }

        dtypep = applyPackedRanges(fl, obj_h, dtypep, shared);
        break;
    }
    case vpiArrayVar: {
        auto typespec_h = vpi_handle(vpiTypespec, obj_h);
        if (typespec_h) {
            dtypep = getDType(fl, typespec_h, shared);
        } else {  // Try to get the type from one of the elements
            auto itr = vpi_iterate(vpiReg, obj_h);
            auto member_h = vpi_scan(itr);
            typespec_h = vpi_handle(vpiTypespec, member_h);
            if (typespec_h) {
                dtypep = getDType(fl, typespec_h, shared);
            } else {
                dtypep = getDType(fl, member_h, shared);
            }
            vpi_release_handle(itr);
            vpi_release_handle(member_h);
        }
        vpi_release_handle(typespec_h);

        dtypep = applyUnpackedRanges(make_fileline(obj_h), obj_h, dtypep, shared);
        break;
    }
    case vpiArrayNet: {
        vpiHandle itr = vpi_iterate(vpiNet, obj_h);
        if (vpiHandle vpi_child_obj = vpi_scan(itr)) {
            dtypep = getDType(fl, vpi_child_obj, shared);
            vpi_release_handle(vpi_child_obj);
        }
        vpi_release_handle(itr);

        dtypep = applyUnpackedRanges(make_fileline(obj_h), obj_h, dtypep, shared);
        break;
    }
    case vpiRefVar: {
        auto* name = vpi_get_str(vpiName, obj_h);
        return new AstRefDType(fl, name);
    }
    default: v3error("Unknown object type: " << UHDM::VpiTypeName(obj_h));
    }
    return dtypep;
}

AstAlways* process_always(vpiHandle obj_h, UhdmShared& shared) {
    VAlwaysKwd alwaysType;
    // Which always type is it?
    switch (vpi_get(vpiAlwaysType, obj_h)) {
    case vpiAlways: {
        alwaysType = VAlwaysKwd::ALWAYS;
        break;
    }
    case vpiAlwaysFF: {
        alwaysType = VAlwaysKwd::ALWAYS_FF;
        break;
    }
    case vpiAlwaysLatch: {
        alwaysType = VAlwaysKwd::ALWAYS_LATCH;
        break;
    }
    case vpiAlwaysComb: {
        alwaysType = VAlwaysKwd::ALWAYS_COMB;
        break;
    }
    default: {
        v3error("Unhandled always type");
        break;
    }
    }

    // Body of always statement
    AstNode* bodyp = nullptr;
    visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* nodep) { bodyp = nodep; });
    return new AstAlways(make_fileline(obj_h), alwaysType, nullptr, bodyp);
}

AstTimingControl* process_event_control(vpiHandle obj_h, UhdmShared& shared) {
    AstSenItem* senItemRootp = nullptr;
    visit_one_to_one({vpiCondition}, obj_h, shared, [&](AstNode* nodep) {
        if (nodep->type() == AstType::en::atSenItem) {
            senItemRootp = reinterpret_cast<AstSenItem*>(nodep);
        } else {  // wrap this in a AstSenItem
            senItemRootp = new AstSenItem(nodep->fileline(), VEdgeType::ET_ANYEDGE, nodep);
        }
    });
    AstSenTree* senTreep = new AstSenTree(make_fileline(obj_h), senItemRootp);
    // Body of statements
    AstNode* bodyp = nullptr;
    visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* nodep) { bodyp = nodep; });
    return new AstTimingControl(make_fileline(obj_h), senTreep, bodyp);
}

AstNode* process_operation(vpiHandle obj_h, UhdmShared& shared, std::vector<AstNode*>&& operands) {
    if (vpi_get(vpiReordered, obj_h)) {
        // this field is present when Surelog changed the order of array parameters
        // It happens when subarray is selected from multidimensional parameter
        std::reverse(operands.begin(), operands.end());
    }

    auto operation = vpi_get(vpiOpType, obj_h);
    switch (operation) {
    case vpiBitNegOp: {
        return new AstNot(make_fileline(obj_h), operands[0]);
    }
    case vpiNotOp: {
        return new AstLogNot(make_fileline(obj_h), operands[0]);
    }
    case vpiBitAndOp: {
        return new AstAnd(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiListOp: {
        AstNode* elementp = operands[0];
        // First operand is assigned above, start from second
        for (auto it = ++operands.begin(); it != operands.end(); it++) {
            elementp->addNextNull(*it);
        }
        return elementp;
    }
    case vpiBitOrOp: {
        return new AstOr(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiBitXorOp: {
        return new AstXor(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiBitXnorOp: {
        return new AstNot(make_fileline(obj_h), new AstXor(make_fileline(obj_h), operands[0], operands[1]));
    }
    case vpiImplyOp: {
        // Unsupported by mainline verilator
        // return new AstImplication(make_fileline(obj_h), operands[0], operands[1]);
        make_fileline(obj_h)->v3error("Implication operator is unsupported");
    }
    case vpiPostIncOp:
    case vpiPostDecOp: {
        auto* onep = new AstConst(make_fileline(obj_h), 1);
        AstNode* op = nullptr;
        if (operation == vpiPostIncOp) {
            op = new AstAdd(make_fileline(obj_h), operands[0], onep);
        } else if (operation == vpiPostDecOp) {
            op = new AstSub(make_fileline(obj_h), operands[0], onep);
        }
        auto* varp = get_referenceNode(make_fileline(obj_h), operands[0]->name(), shared);
        return new AstAssign(make_fileline(obj_h), varp, op);
    }
    case vpiAssignmentOp: {
        return new AstAssign(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiUnaryAndOp: {
        return new AstRedAnd(make_fileline(obj_h), operands[0]);
    }
    case vpiUnaryNandOp: {
        auto* op = new AstRedAnd(make_fileline(obj_h), operands[0]);
        return new AstNot(make_fileline(obj_h), op);
    }
    case vpiUnaryNorOp: {
        auto* op = new AstRedOr(make_fileline(obj_h), operands[0]);
        return new AstNot(make_fileline(obj_h), op);
    }
    case vpiUnaryOrOp: {
        return new AstRedOr(make_fileline(obj_h), operands[0]);
    }
    case vpiUnaryXorOp: {
        return new AstRedXor(make_fileline(obj_h), operands[0]);
    }
    case vpiUnaryXNorOp: {
        return new AstNot(make_fileline(obj_h), new AstRedXor(make_fileline(obj_h), operands[0]));
    }
    case vpiEventOrOp: {
        // Do not create a separate node
        // Chain operand nodes instead
        AstNode* eventOrNodep = nullptr;
        for (auto op : operands) {
            if (op) {
                if (op->type() == AstType::en::atSenItem) {
                    // This is a Posedge/Negedge operation, keep this op
                    if (eventOrNodep == nullptr) {
                        eventOrNodep = op;
                    } else {
                        eventOrNodep->addNextNull(op);
                    }
                } else {
                    // Edge not specified -> use ANY
                    auto* wrapperp
                        = new AstSenItem(make_fileline(obj_h), VEdgeType::ET_ANYEDGE, op);
                    if (eventOrNodep == nullptr) {
                        eventOrNodep = wrapperp;
                    } else {
                        eventOrNodep->addNextNull(wrapperp);
                    }
                }
            }
        }
        return eventOrNodep;
    }
    case vpiLogAndOp: {
        return new AstLogAnd(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiLogOrOp: {
        return new AstLogOr(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiPosedgeOp: {
        return new AstSenItem(make_fileline(obj_h), VEdgeType::ET_POSEDGE, operands[0]);
    }
    case vpiNegedgeOp: {
        return new AstSenItem(make_fileline(obj_h), VEdgeType::ET_NEGEDGE, operands[0]);
    }
    case vpiEqOp: {
        return new AstEq(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiCaseEqOp: {
        return new AstEqCase(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiNeqOp: {
        return new AstNeq(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiCaseNeqOp: {
        return new AstNeqCase(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiWildEqOp: {
        return new AstEqWild(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiWildNeqOp: {
        return new AstNeqWild(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiGtOp: {
        return new AstGt(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiGeOp: {
        return new AstGte(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiLtOp: {
        return new AstLt(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiLeOp: {
        return new AstLte(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiPlusOp: {
        return operands[0];
    }
    case vpiSubOp: {
        return new AstSub(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiMinusOp: {
        return new AstNegate(make_fileline(obj_h), operands[0]);
    }
    case vpiAddOp: {
        return new AstAdd(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiMultOp: {
        return new AstMul(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiDivOp: {
        return new AstDiv(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiModOp: {
        return new AstModDiv(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiConditionOp: {
        return new AstCond(make_fileline(obj_h), operands[0], operands[1], operands[2]);
    }
    case vpiConcatOp: {
        AstNode* op1p = nullptr;
        AstNode* op2p = nullptr;
        for (auto op : operands) {
            if (op != nullptr) {
                if (op1p == nullptr) {
                    op1p = op;
                } else if (op2p == nullptr) {
                    op2p = op;
                } else {
                    // Add one more level
                    op1p = new AstConcat(make_fileline(obj_h), op1p, op2p);
                    op2p = op;
                }
            }
        }
        // The following case doesn't require wrapping in AstReplicate
        if (op2p == nullptr && VN_IS(op1p, Const))
            return op1p;
        // Wrap in a Replicate node
        if (op2p != nullptr) {
            op1p = new AstConcat(make_fileline(obj_h), op1p, op2p);
            op2p = new AstConst(make_fileline(obj_h), 1);
        } else {
            op2p = new AstConst(make_fileline(obj_h), 1);
        }
        return new AstReplicate(make_fileline(obj_h), op1p, op2p);
    }
    case vpiMultiConcatOp: {
        // Sides in AST are switched: first value, then count
        return new AstReplicate(make_fileline(obj_h), operands[1], operands[0]);
    }
    case vpiArithLShiftOp:  // This behaves the same as normal shift
    case vpiLShiftOp: {
        return new AstShiftL(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiRShiftOp: {
        return new AstShiftR(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiArithRShiftOp: {
        return new AstShiftRS(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiInsideOp: {
        AstNode* exprp = operands[0];
        AstNode* itemsp = operands[1];
        for (auto it = operands.begin() + 2; it != operands.end(); it++) {
            itemsp->addNextNull(*it);
        }
        return new AstInside(make_fileline(obj_h), exprp, itemsp);
    }
    case vpiCastOp: {
        auto typespec_h = vpi_handle(vpiTypespec, obj_h);
        auto type = vpi_get(vpiType, typespec_h);
        AstNode* sizeNodep = nullptr;
        if (type == vpiIntTypespec || type == vpiIntegerTypespec) {
            if (vpiHandle expr_h = vpi_handle(vpiExpr, typespec_h)) {
                sizeNodep = visit_object(expr_h, shared);
                vpi_release_handle(expr_h);
            } else if (auto* namep = vpi_get_str(vpiName, typespec_h))
                sizeNodep = new AstParseRef(make_fileline(typespec_h), VParseRefExp::en::PX_TEXT,
                                            namep, nullptr, nullptr);
            else
                sizeNodep = get_value_as_node(typespec_h);
        }

        if (sizeNodep != nullptr) {
            return new AstCastParse(make_fileline(obj_h), operands[0], sizeNodep);
        } else {
            AstNodeDType* dtypep = getDType(make_fileline(obj_h), typespec_h, shared);
            return new AstCast(make_fileline(obj_h), operands[0], VFlagChildDType(), dtypep);
        }
    }
    case vpiStreamRLOp: {
        // Verilog {op0{op1}} - Note op0 is the slice size, not the op1
        // IEEE 11.4.14.2: If a slice_size is not specified, the default is 1.
        if (operands.size() == 1) {
            return new AstStreamL(make_fileline(obj_h), operands[0],
                                  new AstConst(make_fileline(obj_h), 1));
        } else {
            return new AstStreamL(make_fileline(obj_h), operands[1], operands[0]);
        }
    }
    case vpiStreamLROp: {
        // See comments above - default slice size is 1
        if (operands.size() == 1) {
            return new AstStreamR(make_fileline(obj_h), operands[0],
                                  new AstConst(make_fileline(obj_h), 1));
        } else {
            return new AstStreamR(make_fileline(obj_h), operands[1], operands[0]);
        }
    }
    case vpiPowerOp: {
        return new AstPow(make_fileline(obj_h), operands[0], operands[1]);
    }
    case vpiAssignmentPatternOp: {
        AstNode* itemsp = nullptr;
        for (auto op : operands) {
            // Wrap only if this is a positional pattern
            // Tagged patterns will return member nodes
            if (op && !VN_IS(op, PatMember)) {
                op = new AstPatMember(make_fileline(obj_h), op, nullptr, nullptr);
            }
            if (itemsp == nullptr) {
                itemsp = op;
            } else {
                itemsp->addNextNull(op);
            }
        }
        auto patternp = new AstPattern(make_fileline(obj_h), itemsp);
        if (auto typespec_h = vpi_handle(vpiTypespec, obj_h)) {
            AstNodeDType* dtypep = getDType(make_fileline(obj_h), typespec_h, shared);
            patternp->childDTypep(dtypep);
            vpi_release_handle(typespec_h);
        }
        return patternp;
    }
    case vpiMultiAssignmentPatternOp: {
        // '{op0{op1}}
        AstPatMember* patMemberp = nullptr;
        // in case of '{op0{op1, op2, ..., opn}}
        // Verilator forms a list from them via addNext method
        // and passes it as argument to constructor
        // but Surelog returns op1, ..., opn as vpiConcatOp
        // We need to detect that case, because it causes problems
        vpiHandle operands_itr = vpi_iterate(vpiOperand, obj_h);
        vpiHandle operand_h = vpi_scan(operands_itr);
        vpi_release_handle(operand_h);
        // we need to know only the type of 2nd operand
        operand_h = vpi_scan(operands_itr);
        if (vpi_get(vpiType, operand_h) == vpiOperation
            && vpi_get(vpiOpType, operand_h) == vpiConcatOp) {
            AstNode* elementsToReplicatep = nullptr;
            visit_one_to_many({vpiOperand}, operand_h, shared, [&](AstNode* itemp) {
                if (itemp) {
                    if (elementsToReplicatep)
                        elementsToReplicatep->addNext(itemp);
                    else
                        elementsToReplicatep = itemp;
                }
            });
            operands[1]->deleteTree();
            operands[1] = elementsToReplicatep;
        }
        vpi_release_handle(operand_h);
        vpi_release_handle(operands_itr);

        patMemberp = new AstPatMember(make_fileline(obj_h), operands[1], nullptr, operands[0]);
        return new AstPattern(make_fileline(obj_h), patMemberp);
    }
    case vpiNullOp: {
        return nullptr;
    }
    default: {
        v3error("\t! Encountered unhandled operation: " << operation);
        break;
    }
    }
    return nullptr;
}

AstNode* process_assignment(vpiHandle obj_h, UhdmShared& shared) {
    AstNode* lvaluep = nullptr;
    AstNode* rvaluep = nullptr;
    const unsigned int objectType = vpi_get(vpiType, obj_h);
    const unsigned int operationType = vpi_get(vpiOpType, obj_h);

    // Right
    visit_one_to_one({vpiRhs}, obj_h, shared, [&](AstNode* childp) { rvaluep = childp; });

    // Left
    visit_one_to_one({vpiLhs}, obj_h, shared, [&](AstNode* childp) { lvaluep = childp; });

    const unsigned int arithmeticAssignmentOpTypes[]
        = {vpiBitAndOp, vpiBitOrOp,       vpiBitXorOp, vpiBitXnorOp, vpiLogAndOp,
           vpiLogOrOp,  vpiSubOp,         vpiAddOp,    vpiMultOp,    vpiDivOp,
           vpiModOp,    vpiArithLShiftOp, vpiLShiftOp, vpiRShiftOp,  vpiArithRShiftOp};
    if (std::find(std::begin(arithmeticAssignmentOpTypes), std::end(arithmeticAssignmentOpTypes),
                  operationType)
        != std::end(arithmeticAssignmentOpTypes)) {
        rvaluep = process_operation(obj_h, shared, {lvaluep, rvaluep});
        lvaluep = lvaluep->cloneTree(true);
    }

    if (rvaluep != nullptr && rvaluep->type() == AstType::en::atFOpen) {
        // Not really an assignment, AstFOpen node takes care of the lhs
        return rvaluep;
    }
    if (lvaluep && rvaluep) {
        if (objectType == vpiAssignment) {
            auto blocking = vpi_get(vpiBlocking, obj_h);
            if (blocking) {
                return new AstAssign(make_fileline(obj_h), lvaluep, rvaluep);
            } else {
                return new AstAssignDly(make_fileline(obj_h), lvaluep, rvaluep);
            }
        } else {
            AstNode* assignp;
            if (AstVar* varp = VN_CAST(lvaluep, Var)) {
                // Assign on variable declaration
                if (varp->varType() != AstVarType::VAR && objectType == vpiContAssign) {
                    // Return both the variable and assignment
                    assignp = new AstAssignW(make_fileline(obj_h),
                            new AstVarRef(make_fileline(obj_h), varp->name(), VAccess::WRITE),
                            rvaluep);
                    varp->addNextNull(assignp);
                    return varp;
                } else {
                    // Set initial value to a variable and return it
                    varp->valuep(rvaluep);
                    return varp;
                }
            } else {
                if (objectType == vpiContAssign)
                    assignp = new AstAssignW(make_fileline(obj_h), lvaluep, rvaluep);
                else
                    assignp = new AstAssign(make_fileline(obj_h), lvaluep, rvaluep);
                return assignp;
            }
        }
    }
    v3error("Failed to handle assignment");
    return nullptr;
}

AstNode* process_genScopeArray(vpiHandle obj_h, UhdmShared& shared) {
    AstNode* statementsp = nullptr;
    std::string objectName = get_object_name(obj_h);

    visit_one_to_many({vpiGenScope}, obj_h, shared, [&](AstNode* itemp) {
        if (statementsp == nullptr) {
            statementsp = itemp;
        } else {
            statementsp->addNextNull(itemp);
        }
    });
    // Cheat here a little:
    // UHDM already provides us with a correct, elaborated branch only, but then we lose
    // hierarchy for named scopes. Create here an always-true scope that will be expanded
    // by Verilator later, preserving naming hierarchy.
    if (objectName != "") {
        auto* truep = new AstConst(make_fileline(obj_h), AstConst::Unsized32(), 1);
        auto* blockp = new AstBegin(make_fileline(obj_h), objectName, statementsp, true, false);
        auto* scopep = new AstGenIf(make_fileline(obj_h), truep, blockp, nullptr);
        return scopep;
    } else {
        return new AstBegin(make_fileline(obj_h), "", statementsp);
    }
}

AstMethodCall* process_method_call(vpiHandle obj_h, AstNode* fromp, UhdmShared& shared) {
    // Surelog sometimes doesn't use vpiPrefix field to pass the object on which the method is
    // called. Then that object is parsed using vpiHierPath, passed to this function by fromp
    // argument. See https://github.com/chipsalliance/Surelog/issues/2129
    AstNode* argsp = nullptr;
    if (fromp == nullptr) {
        if (vpiHandle prefix_h = vpi_handle(vpiPrefix, obj_h)) {
            std::string refName = get_object_name(prefix_h);
            fromp = get_referenceNode(make_fileline(prefix_h), refName, shared);
            vpi_release_handle(prefix_h);
        } else {
            fromp = new AstParseRef(make_fileline(obj_h), VParseRefExp::en::PX_TEXT, "this",
                                    nullptr, nullptr);
        }
    }
    visit_one_to_many({vpiArgument}, obj_h, shared, [&](AstNode* itemp) {
        AstNode* argp = new AstArg(make_fileline(obj_h), "", itemp);
        if (argsp == nullptr) {
            argsp = argp;
        } else {
            argsp->addNextNull(argp);
        }
    });
    std::string methodName = get_object_name(obj_h);
    return new AstMethodCall(make_fileline(obj_h), fromp, methodName, argsp);
}

AstNode* process_hierPath(vpiHandle obj_h, UhdmShared& shared) {
    AstNode* hierPathp = nullptr;
    AstNode* hierItemp = nullptr;
    FileLine* fl = make_fileline(obj_h);
    bool expr_const_present = false;
    std::string objectName;
    
    if (vpiHandle expr_h = vpi_handle(vpiExpr, obj_h)) {
        if (vpi_get(vpiType, expr_h) == vpiConstant) {
            expr_const_present = true;
            objectName = get_object_name(obj_h);
            objectName = std::regex_replace(objectName, std::regex("\\."), "_");

            AstNode* constp = get_value_as_node(expr_h, true);
            vpiHandle typespec_h = vpi_handle(vpiTypespec, obj_h);
            AstNodeDType* dtypep = getDType(fl, typespec_h, shared);
            vpi_release_handle(typespec_h);

            std::string moduleName = shared.moduleNamesStack.top();
            AstVar* temporaryParam = new AstVar(fl, AstVarType::LPARAM, objectName, VFlagChildDType(), dtypep);
            temporaryParam->valuep(constp);

            shared.top_param_map[moduleName][objectName] = temporaryParam;
        }
        vpi_release_handle(expr_h);
    }

    vpiHandle actual_itr = vpi_iterate(vpiActual, obj_h);
    while (vpiHandle actual_h = vpi_scan(actual_itr)) {
        if(vpi_get(vpiType, actual_h) == vpiMethodFuncCall) {
            hierPathp = process_method_call(actual_h, hierPathp, shared);
        } else {
            if (expr_const_present) {
                hierItemp = get_referenceNode(make_fileline(obj_h), objectName, shared);
                expr_const_present = false;
            } else {
                hierItemp = visit_object(actual_h, shared);
            }
            if (hierPathp == nullptr)
                hierPathp = hierItemp;
            else
                hierPathp = new AstDot(fl, false, hierPathp, hierItemp);
        }
        vpi_release_handle(actual_h);
    }
    vpi_release_handle(actual_itr);

    return hierPathp;
}

AstNode* process_ioDecl(vpiHandle obj_h, UhdmShared& shared) {
    std::string objectName = get_object_name(obj_h);

    VDirection dir;
    if (const int n = vpi_get(vpiDirection, obj_h)) {
        if (n == vpiInput) {
            dir = VDirection::INPUT;
        } else if (n == vpiOutput) {
            dir = VDirection::OUTPUT;
        } else if (n == vpiInout) {
            dir = VDirection::INOUT;
        }
        // TODO: vpiMixedIO, vpiNoDirection - not encountered yet
    }
    vpiHandle typedef_h = vpi_handle(vpiTypedef, obj_h);
    AstNodeDType* dtypep = nullptr;
    if (typedef_h) {
        dtypep = getDType(make_fileline(obj_h), typedef_h, shared);
    } else {
        UINFO(7, "No typedef handle found in vpiIODecl" << std::endl);
    }
    if (dtypep == nullptr) {
        UINFO(7, "No dtype found in vpiIODecl, falling back to logic" << std::endl);
        dtypep = new AstBasicDType(make_fileline(obj_h), AstBasicDTypeKwd::LOGIC);
    }

    dtypep = applyUnpackedRanges(make_fileline(obj_h), obj_h, dtypep, shared);

    auto* varp = new AstVar(make_fileline(obj_h), AstVarType::PORT, objectName, VFlagChildDType(),
                            dtypep);
    varp->declDirection(dir);
    varp->direction(dir);
    return varp;
}

AstNode* process_parameter(vpiHandle obj_h, UhdmShared& shared, bool get_value) {
    AstVar* parameterp = nullptr;
    AstNode* parameterValuep = nullptr;

    std::string objectName = get_object_name(obj_h);

    if (get_value) {
        std::string fullName = get_object_name(obj_h, {vpiFullName});
        size_t colon_pos = fullName.rfind("::");
        if (colon_pos != std::string::npos) {
            AstNode* class_pkg_refp
                = get_class_package_ref_node(make_fileline(obj_h), fullName, shared);

            AstNode* var_refp = new AstParseRef(make_fileline(obj_h), VParseRefExp::en::PX_TEXT,
                                                objectName, nullptr, nullptr);
            return AstDot::newIfPkg(make_fileline(obj_h), class_pkg_refp, var_refp);
        }
    }
    if (shared.package_prefix.empty() && is_imported(obj_h)) {
        // Skip imported parameters, they will still be visible in their packages
        // Can't skip in package, as then names from nested imports cannot be resolved
        UINFO(3, "Skipping imported parameter " << objectName << std::endl);
        return nullptr;
    }

    AstNodeDType* dtypep = nullptr;
    auto typespec_h = vpi_handle(vpiTypespec, obj_h);
    if (typespec_h) {
        std::string typespecName = get_object_name(typespec_h);
        // Surelog sometimes inserts parameter name as typespec name
        // We have to detect it to know if we should treat a typespec
        // as type definition or type reference
        if (typespecName == objectName)
            dtypep = VN_CAST(process_typespec(typespec_h, shared), NodeDType);
        else
            dtypep = getDType(make_fileline(typespec_h), typespec_h, shared);

        if (!dtypep)
            v3error("vpiTypespec node of type " << UHDM::VpiTypeName(typespec_h)
                                                << " can't be handled as AstNodeDType");
    } else {
        UINFO(7, "No typespec found in vpiParameter " << objectName << std::endl);

        // If no typespec provided assume default
        dtypep = new AstBasicDType(make_fileline(obj_h), AstBasicDTypeKwd::LOGIC_IMPLICIT);
    }

    if (get_value) { parameterValuep = get_value_as_node(obj_h); }

    AstVarType parameterType;
    int is_local = vpi_get(vpiLocalParam, obj_h);

    if (is_local)
        parameterType = AstVarType::LPARAM;
    else
        parameterType = AstVarType::GPARAM;

    parameterp
        = new AstVar(make_fileline(obj_h), parameterType, objectName, VFlagChildDType(), dtypep);
    if (parameterValuep != nullptr) parameterp->valuep(parameterValuep);
    return parameterp;
}

AstVar* process_param_assign(vpiHandle obj_h, UhdmShared& shared) {
    AstVar* parameterp = nullptr;
    AstNode* parameterValuep = nullptr;

    visit_one_to_one({vpiRhs}, obj_h, shared, [&](AstNode* nodep) { parameterValuep = nodep; });

    vpiHandle parameter_h = vpi_handle(vpiLhs, obj_h);

    if (parameterValuep == nullptr) {
        parameterp = reinterpret_cast<AstVar*>(process_parameter(parameter_h, shared, true));
    } else {
        parameterp = reinterpret_cast<AstVar*>(process_parameter(parameter_h, shared, false));
        if (parameterp != nullptr) { parameterp->valuep(parameterValuep); }
    }

    return parameterp;
}

AstPackageImport* process_uhdm_import(vpiHandle obj_h, UhdmShared& shared) {
    std::string objectName = get_object_name(obj_h);

    AstPackage* packagep = nullptr;
    auto it = shared.package_map.find(objectName);
    if (it != shared.package_map.end()) { packagep = it->second; }
    else { // Create the package if it doesn't exist yet
        packagep = new AstPackage(new FileLine(objectName), objectName);
        shared.package_map.insert(std::make_pair(objectName, packagep));
    }
    std::string symbol_name;
    vpiHandle imported_name = vpi_handle(vpiImport, obj_h);
    if (imported_name) {
        s_vpi_value val;
        vpi_get_value(imported_name, &val);
        symbol_name = val.value.str;
    }
    auto* package_importp = new AstPackageImport(make_fileline(obj_h), packagep, symbol_name);
    shared.m_symp->importItem(packagep, symbol_name);
    return package_importp;
}

AstMemberDType* process_typespec_member(vpiHandle obj_h, UhdmShared& shared) {
    std::string objectName = get_object_name(obj_h);
    AstNodeDType* typespecp = nullptr;
    auto typespec_h = vpi_handle(vpiTypespec, obj_h);
    typespecp = getDType(make_fileline(typespec_h), typespec_h, shared);
    if (typespecp != nullptr) {
        auto* memberp
            = new AstMemberDType(make_fileline(obj_h), objectName, VFlagChildDType(), typespecp);
        return memberp;
    }
    return nullptr;
}

AstNode* process_typespec(vpiHandle obj_h, UhdmShared& shared) {
    if (vpiHandle alias_h = vpi_handle(vpiTypedefAlias, obj_h)) {
        return getDType(make_fileline(obj_h), alias_h, shared);
    }

    std::string objectName = get_object_name(obj_h);
    const unsigned int objectType = vpi_get(vpiType, obj_h);

    auto file_name = vpi_get_str(vpiFile, obj_h);
    const unsigned int currentLine = vpi_get(vpiLineNo, obj_h);
    UINFO(6, __func__ << ": Object: " << objectName << " of type " << objectType << " ("
                      << UHDM::VpiTypeName(obj_h) << ")"
                      << " @ " << currentLine << " : " << (file_name != 0 ? file_name : "?")
                      << std::endl);
    if (file_name) {
        shared.coverage_set.insert({file_name, currentLine, UHDM::VpiTypeName(obj_h)});
    }

    FileLine* fl = make_fileline(obj_h);

    switch (objectType) {
    case vpiBitTypespec:
    case vpiLogicTypespec: {
        AstNodeDType* dtypep = nullptr;
        if (auto elem_typespec_h = vpi_handle(vpiElemTypespec, obj_h)) {
            dtypep = getDType(fl, elem_typespec_h, shared);
            if (!dtypep) v3error("Unable to handle vpiElemTypespec node");
        } else {
            AstBasicDTypeKwd keyword = get_kwd_for_type(objectType);
            dtypep = new AstBasicDType(fl, keyword);
        }
        dtypep = applyPackedRanges(fl, obj_h, dtypep, shared);
        return dtypep;
    }
    case vpiIntTypespec:
    case vpiLongIntTypespec:
    case vpiIntegerTypespec:
    case vpiShortIntTypespec:
    case vpiShortRealTypespec:
    case vpiByteTypespec:
    case vpiRealTypespec:
    case vpiStringTypespec:
    case vpiChandleTypespec:
    case vpiTimeTypespec: {
        AstBasicDTypeKwd keyword = get_kwd_for_type(objectType);
        return new AstBasicDType(fl, keyword);
    }
    case vpiVoidTypespec: {
        return new AstVoidDType(fl);
    }
    case vpiArrayTypespec: {
        auto elem_typespec_h = vpi_handle(vpiElemTypespec, obj_h);
        AstNodeDType* dtypep = getDType(fl, elem_typespec_h, shared);
        return applyUnpackedRanges(fl, obj_h, dtypep, shared);
    }
    case vpiPackedArrayTypespec: {
        AstNodeDType* dtypep = nullptr;
        auto elem_typespec_h = vpi_handle(vpiElemTypespec, obj_h);
        if (elem_typespec_h) {
            dtypep = getDType(fl, elem_typespec_h, shared);
        } else {
            UINFO(7, "No elem_typespec found in vpiPackedArrayTypespec, trying IndexTypespec"
                         << std::endl);
            auto index_typespec_h = vpi_handle(vpiIndexTypespec, obj_h);
            if (index_typespec_h) {
                dtypep = getDType(fl, index_typespec_h, shared);
            } else {
                v3error("Failed to get typespec handle for PackedArrayTypespec");
            }
        }
        return applyPackedRanges(fl, obj_h, dtypep, shared);
    }
    case vpiEnumTypespec: {
        const uhdm_handle* const handle = (const uhdm_handle*)obj_h;
        const UHDM::BaseClass* const object = (const UHDM::BaseClass*)handle->object;
        if (shared.visited_types_map.find(object) != shared.visited_types_map.end()) {
            // Already seen this, do not create a duplicate
            // References are handled using getDType, not in visit_object
            return nullptr;
        }

        shared.visited_types_map[object] = objectName;

        // Use bare name for typespec itself, hierarchy was stored above
        auto pos = objectName.rfind("::");
        if (pos != std::string::npos) objectName = objectName.substr(pos + 2);

        AstNode* enum_members = nullptr;
        AstNodeDType* enum_member_dtype = nullptr;

        vpiHandle itr = vpi_iterate(vpiEnumConst, obj_h);
        while (vpiHandle item_h = vpi_scan(itr)) {
            std::string item_name = get_object_name(item_h);

            auto* value = get_value_as_node(item_h, false);
            auto* wrapped_item = new AstEnumItem(make_fileline(item_h), item_name, nullptr, value);
            if (enum_members == nullptr) {
                enum_members = wrapped_item;
            } else {
                enum_members->addNextNull(wrapped_item);
            }
        }
        vpi_release_handle(itr);

        visit_one_to_one({vpiBaseTypespec}, obj_h, shared, [&](AstNode* item) {
            if (item != nullptr) { enum_member_dtype = reinterpret_cast<AstNodeDType*>(item); }
        });
        if (enum_member_dtype == nullptr) {
            // No data type specified, use default
            enum_member_dtype = new AstBasicDType(fl, AstBasicDTypeKwd::INT);
        }
        auto* enum_dtype
            = new AstEnumDType(fl, VFlagChildDType(), enum_member_dtype, enum_members);
        auto* dtype
            = new AstDefImplicitDType(fl, objectName, nullptr, VFlagChildDType(), enum_dtype);
        return dtype;
    }
    case vpiStructTypespec:
    case vpiUnionTypespec: {
        const uhdm_handle* const handle = (const uhdm_handle*)obj_h;
        const UHDM::BaseClass* const object = (const UHDM::BaseClass*)handle->object;
        if (shared.visited_types_map.find(object) != shared.visited_types_map.end()) {
            UINFO(6, "Object " << objectName << " was already visited" << std::endl);
            return nullptr;
        }

        shared.visited_types_map[object] = objectName;

        // Use bare name for typespec itself, hierarchy was stored above
        auto pos = objectName.rfind("::");
        if (pos != std::string::npos) objectName = objectName.substr(pos + 2);

        // VSigning below is used in AstStructDtype to indicate
        // if packed or not
        VSigning packed;
        if (vpi_get(vpiPacked, obj_h)) {
            packed = VSigning::SIGNED;
        } else {
            packed = VSigning::UNSIGNED;
        }
        AstNodeUOrStructDType* structOrUnionDTypep = nullptr;
        if (objectType == vpiStructTypespec)
            structOrUnionDTypep = new AstStructDType(fl, packed);
        else
            structOrUnionDTypep = new AstUnionDType(fl, packed);

        vpiHandle member_itr = vpi_iterate(vpiTypespecMember, obj_h);
        while (vpiHandle member_obj = vpi_scan(member_itr)) {
            AstMemberDType* memberp = process_typespec_member(member_obj, shared);
            if (memberp != nullptr) structOrUnionDTypep->addMembersp(memberp);
        }

        auto* dtypep
            = new AstDefImplicitDType(fl, objectName, nullptr, VFlagChildDType(), structOrUnionDTypep);
        return dtypep;
    }
    case vpiUnsupportedTypespec: {
        auto* fl = make_fileline(obj_h);
        fl->v3info("\t! This typespec is unsupported in UHDM: " << file_name << ":" << currentLine);
        // Create a reference and try to resolve later
        return get_referenceNode(make_fileline(obj_h), objectName, shared);
    }
    }
    return nullptr;
}

AstNode* process_typedef(vpiHandle obj_h, UhdmShared& shared) {
    const unsigned int type = vpi_get(vpiType, obj_h);
    if (type == UHDM::uhdmimport) {
        // imports are under vpiTypedef nodes, but they are not defined types
        return process_uhdm_import(obj_h, shared);
    }

    std::string objectName = get_object_name(obj_h);

    auto pos = objectName.rfind("::");
    if (pos != std::string::npos) {
        std::string packageName = objectName.substr(0, pos + 2);
        std::string baseName = objectName.substr(pos + 2);
        if (packageName != shared.package_prefix) {
            return get_type_reference(make_fileline(obj_h), baseName, objectName, shared);
        } else {
            objectName = baseName;
        }
    }

    AstNodeDType* refp = nullptr;
    if (vpiHandle alias_h = vpi_handle(vpiTypedefAlias, obj_h)) {
        refp = getDType(make_fileline(alias_h), alias_h, shared);
    } else {
        refp = reinterpret_cast<AstNodeDType*>(process_typespec(obj_h, shared));
        if (refp == nullptr) {
            UINFO(7, "Typedef revisited: " << objectName << ", skipping" << std::endl);
            return nullptr;
        }
    }

    AstTypedef* typedefp
        = new AstTypedef(make_fileline(obj_h), objectName, nullptr, VFlagChildDType(), refp);

    shared.m_symp->reinsert(typedefp);
    return typedefp;
}

AstNode* process_scope(vpiHandle obj_h, UhdmShared& shared, AstNode* bodyp = nullptr) {
    vpiHandle typedef_itr = vpi_iterate(vpiTypedef, obj_h);
    while (vpiHandle typedef_obj = vpi_scan(typedef_itr)) {
        AstNode* typedefp = process_typedef(typedef_obj, shared);
        if (bodyp == nullptr)
            bodyp = typedefp;
        else
            bodyp->addNextNull(typedefp);
        vpi_release_handle(typedef_obj);
    }
    vpi_release_handle(typedef_itr);

    visit_one_to_many(
        {
            vpiPropertyDecl,
            vpiSequenceDecl,
            vpiConcurrentAssertions,
            vpiNamedEvent,
            vpiNamedEventArray,
            vpiVariables,
            vpiVirtualInterfaceVar,
            vpiReg,
            vpiRegArray,
            vpiMemory,
            vpiParamAssign,
            vpiInternalScope,
            vpiImport,
            vpiLetDecl
        },
        obj_h, shared, [&](AstNode* nodep) {
            if (bodyp == nullptr) {
                bodyp = nodep;
            } else {
                bodyp->addNextNull(nodep);
            }
        });
    return bodyp;
}

AstNode* process_function_task(vpiHandle obj_h, UhdmShared& shared) {
    AstNodeFTask* taskFuncp = nullptr;

    std::string objectName = get_object_name(obj_h);

    const uhdm_handle* const handle = (const uhdm_handle*)obj_h;
    const UHDM::BaseClass* const object = (const UHDM::BaseClass*)handle->object;
    if (shared.visited_objects.find(object) != shared.visited_objects.end()) {
        // Surelog sometimes copies function instead of creating reference under vpiImport node
        return nullptr;
    }
    shared.visited_objects.insert(object);

    AstNode* statementsp = nullptr;
    visit_one_to_many({vpiIODecl}, obj_h, shared, [&](AstNode* itemp) {
        if (itemp) {
            if (statementsp)
                statementsp->addNextNull(itemp);
            else
                statementsp = itemp;
        }
    });

    statementsp = process_scope(obj_h, shared, statementsp);

    visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* itemp) {
        if (itemp) {
            if (statementsp)
                statementsp->addNextNull(itemp);
            else
                statementsp = itemp;
        }
    });

    if (auto return_h = vpi_handle(vpiReturn, obj_h)) {
        AstNodeDType* returnDTypep = getDType(make_fileline(obj_h), return_h, shared);
        taskFuncp = new AstFunc(make_fileline(obj_h), objectName, statementsp, returnDTypep);
    } else {
        taskFuncp = new AstTask(make_fileline(obj_h), objectName, statementsp);
    }

    if (vpi_get(vpiDPIContext, obj_h)) taskFuncp->dpiContext(true);
    if (vpi_get(vpiDPIPure, obj_h)) taskFuncp->pure(true);

    auto accessType = vpi_get(vpiAccessType, obj_h);
    if (accessType == vpiDPIExportAcc) {
        AstDpiExport* exportp = new AstDpiExport(make_fileline(obj_h), objectName, objectName);
        exportp->addNext(taskFuncp);
        v3Global.dpi(true);
        return exportp;
    } else if (accessType == vpiDPIImportAcc) {
        taskFuncp->dpiImport(true);
        v3Global.dpi(true);
        if (vpi_get(vpiType, obj_h) == vpiTask) {
            AstTask* taskp = reinterpret_cast<AstTask*>(taskFuncp);
            taskp->dpiTask(true);
        }
        if (taskFuncp->prettyName()[0] == '$')
            shared.m_symp->reinsert(taskFuncp, nullptr, taskFuncp->prettyName());
        shared.m_symp->reinsert(taskFuncp);
    }
    return taskFuncp;
}

AstNode* vectorToAstList(std::vector<AstNode*>::const_iterator begin, std::vector<AstNode*>::const_iterator end) {
    AstNode* nodep = nullptr;
    for (auto it = begin; it != end; it++)
        nodep = AstNode::addNext(nodep, *it);
    return nodep;
}

AstNode* vectorToAstList(const std::vector<AstNode*>& nodes) {
    return vectorToAstList(nodes.begin(), nodes.end());
}

AstNode* visit_object(vpiHandle obj_h, UhdmShared& shared) {
    // Will keep current node
    AstNode* node = nullptr;

    // Current object data
    int lineNo = 0;

    // For iterating over child objects
    vpiHandle itr;

    std::string objectName = get_object_name(obj_h, {vpiName, vpiFullName, vpiDefName});
    std::string fullObjectName = get_object_name(obj_h, {vpiFullName});

    auto file_name = vpi_get_str(vpiFile, obj_h);

    if (unsigned int l = vpi_get(vpiLineNo, obj_h)) { lineNo = l; }

    const unsigned int currentLine = vpi_get(vpiLineNo, obj_h);
    const unsigned int objectType = vpi_get(vpiType, obj_h);
    UINFO(6, "Object: " << objectName << " of type " << objectType << " ("
                        << UHDM::VpiTypeName(obj_h) << ")"
                        << " @ " << currentLine << " : " << (file_name != 0 ? file_name : "?")
                        << std::endl);
    if (file_name) {
        shared.coverage_set.insert({file_name, currentLine, UHDM::VpiTypeName(obj_h)});
    }

    switch (objectType) {
    case vpiDesign: {

        visit_one_to_many({UHDM::uhdmallInterfaces, UHDM::uhdmtopModules}, obj_h, shared,
                          [&](AstNode* module) {
                              if (module != nullptr) { node = module; }
                          });
        return node;
    }
    case vpiPackage: {
        AstPackage* package = nullptr;
        auto it = shared.package_map.find(objectName); // In case it has been created because of an import
        if (it != shared.package_map.end()) package = it->second;
        else package = new AstPackage(new FileLine(objectName), objectName);
        package->inLibrary(true);
        shared.package_prefix = objectName + "::";
        shared.m_symp->pushNew(package);

        vpiHandle typedef_itr = vpi_iterate(vpiTypedef, obj_h);
        while (vpiHandle typedef_obj = vpi_scan(typedef_itr)) {
            AstNode* typedefp = process_typedef(typedef_obj, shared);
            if (typedefp != nullptr) package->addStmtp(typedefp);
        }

        visit_one_to_many(
            {
                vpiParamAssign,
                vpiProgram,
                vpiProgramArray,
                vpiTaskFunc,
                vpiSpecParam,
                vpiAssertion,
            },
            obj_h, shared, [&](AstNode* item) {
                if (item != nullptr) { package->addStmtp(item); }
            });
        shared.m_symp->popScope(package);
        shared.package_prefix = shared.package_prefix.substr(0, shared.package_prefix.length()
                                                                    - (objectName.length() + 2));

        shared.package_map[objectName] = package;
        return package;
    }
    case vpiPort: {
        static unsigned numPorts;
        AstPort* port = nullptr;
        AstVar* var = nullptr;

        AstNodeDType* dtype = nullptr;
        auto parent_h = vpi_handle(vpiParent, obj_h);
        std::string netName = "";
        for (auto net : {vpiNet, vpiNetArray, vpiArrayNet, vpiVariables}) {
            vpiHandle itr = vpi_iterate(net, parent_h);
            while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
                netName = get_object_name(vpi_child_obj);
                UINFO(7, "Net name is " << netName << std::endl);
                if (netName == objectName) {
                    UINFO(7, "Found matching net for " << objectName << std::endl);
                    dtype = getDType(make_fileline(obj_h), vpi_child_obj, shared);
                    break;
                }
                vpi_release_handle(vpi_child_obj);
            }
            vpi_release_handle(itr);
        }
        if (dtype == nullptr) {
            // If no matching net was found, get info from port node connections
            // This is the case for interface ports
            dtype = getDType(make_fileline(obj_h), obj_h, shared);
        }
        if (VN_IS(dtype, IfaceRefDType)) {
            var = new AstVar(make_fileline(obj_h), AstVarType::IFACEREF, objectName,
                             VFlagChildDType(), dtype);
        } else {
            var = new AstVar(make_fileline(obj_h), AstVarType::PORT, objectName, VFlagChildDType(),
                             dtype);

            if (const int n = vpi_get(vpiDirection, obj_h)) {
                UINFO(6, "Got direction for " << objectName << std::endl);
                if (n == vpiInput) {
                    var->declDirection(VDirection::INPUT);
                    var->direction(VDirection::INPUT);
                    var->varType(AstVarType::PORT);
                } else if (n == vpiOutput) {
                    var->declDirection(VDirection::OUTPUT);
                    var->direction(VDirection::OUTPUT);
                    var->varType(AstVarType::PORT);
                } else if (n == vpiInout) {
                    var->declDirection(VDirection::INOUT);
                    var->direction(VDirection::INOUT);
                }
            } else {
                UINFO(6, "Got no direction for " << objectName << ", skipping");
                return nullptr;
            }
        }

        port = new AstPort(make_fileline(obj_h), ++numPorts, objectName);
        port->addNextNull(var);

        if (v3Global.opt.trace()) { var->trace(true); }

        return port;
    }
    case UHDM::uhdmimport: {
        return process_uhdm_import(obj_h, shared);
    }
    case vpiModule: {
        std::string modDefName = get_object_name(obj_h, {vpiDefName});
        std::string modType = modDefName;
        shared.moduleNamesStack.push(modDefName);
        remove_scope(modType);
        AstModule* module;

        // Check if we have encountered this object before
        auto it = shared.top_nodes.find(modType);
        auto param_it = shared.top_param_map.find(modDefName);
        if (it != shared.top_nodes.end()) {
            // Was created before, fill missing
            module = reinterpret_cast<AstModule*>(it->second);

            // If available, check vpiFullName instead of vpiName, as vpiName can equal vpiDefName
            std::string fullName = objectName;
            if (auto* s = vpi_get_str(vpiFullName, obj_h)) {
                fullName = s;
                sanitize_str(fullName);
            }
            module->user1(false);  // Not partial anymore (potentially)
            if (fullName != modDefName) { // Not a top module
                itr = vpi_iterate(vpiParameter, obj_h);
                while (vpiHandle param_h = vpi_scan(itr)) {
                    if (!vpi_get(vpiLocalParam, param_h) && !is_imported(param_h)) {
                        module->user1(true); // Need to set params, mark as partial again
                        vpi_release_handle(param_h);
                        break;
                    }
                    vpi_release_handle(param_h);
                }
                vpi_release_handle(itr);
            }
            if (module->user1u().toInt()) { // Is partial
                static int module_counter;
                // Create separate node with proper params
                module = module->cloneTree(false);
                module->user1(false);  // Not partial anymore
                module->user4p(nullptr);  // Clear SymEnt
                // Use more specific name
                modType += "_" + objectName + std::to_string(module_counter++);
                module->name(modType);
            }

            if (!module->user2SetOnce()) {  // Only do this once
                shared.m_symp->pushNew(module);

                AstNode* firstNonPortStatementp = module->stmtsp();
                // Ports need to be added before the statements that use them
                visit_one_to_many({vpiPort}, obj_h, shared, [&](AstNode* portp) {
                    if (portp != nullptr) {
                        if (firstNonPortStatementp != nullptr)
                            firstNonPortStatementp->addPrev(portp);
                        else
                            module->addStmtp(portp);
                    }
                });

                visit_one_to_many(
                    {
                        vpiInterface,
                        vpiInterfaceArray,
                        vpiProcess,
                        vpiModule,
                        vpiModuleArray,
                        vpiPrimitive,
                        vpiPrimitiveArray,
                        vpiModPath,
                        vpiTchk,
                        vpiDefParam,
                        vpiIODecl,
                        vpiAliasStmt,
                        vpiClockingBlock,
                        vpiNet,
                        vpiGenScopeArray,
                        vpiArrayNet,

                        // from vpiInstance
                        vpiProgram,
                        vpiProgramArray,
                        vpiTaskFunc,
                        vpiSpecParam,
                        vpiAssertion,
                        // vpiClassDefn,

                        // from vpiScope
                        vpiPropertyDecl,
                        vpiSequenceDecl,
                        vpiConcurrentAssertions,
                        vpiNamedEvent,
                        vpiNamedEventArray,
                        vpiVariables,
                        vpiContAssign,
                        vpiVirtualInterfaceVar,
                        vpiReg,
                        vpiRegArray,
                        vpiMemory,
                        vpiInternalScope,
                        vpiAttribute,
                    },
                    obj_h, shared, [&](AstNode* node) {
                        if (node != nullptr) module->addStmtp(node);
                    });
                // Update parameter values using TopModules tree
                if (param_it != shared.top_param_map.end()) {
                    auto& param_map = param_it->second;
                    visit_one_to_many({vpiParamAssign}, obj_h, shared, [&](AstNode* node) {
                        if (VN_IS(node, Var)) {
                            AstVar* param_node = VN_CAST(node, Var);
                            // Global parameters are added as pins, skip them here
                            if (param_node->varType() == AstVarType::LPARAM)
                                param_map[node->name()] = node;
                        }
                    });
                    // Add final values of parameters
                    for (auto& param_p : param_map) {
                        if (param_p.second != nullptr)
                            module->addStmtp(param_p.second->cloneTree(false));
                    }
                }
                (shared.top_nodes)[modType] = module;
                shared.m_symp->popScope(module);
            }
        } else {
            // Encountered for the first time
            module = new AstModule(new FileLine(modType), modType);
            module->user1(true); // Mark as partial

            vpiHandle typedef_itr = vpi_iterate(vpiTypedef, obj_h);
            while (vpiHandle typedef_obj = vpi_scan(typedef_itr)) {
                AstNode* typedefp = process_typedef(typedef_obj, shared);
                if (typedefp != nullptr) module->addStmtp(typedefp);
            }

            visit_one_to_many(
                {
                    vpiModule,
                    vpiContAssign,
                    vpiProcess,
                    vpiTaskFunc,
                },
                obj_h, shared, [&](AstNode* node) {
                    if (node != nullptr) module->addStmtp(node);
                });

            NameNodeMap param_map;
            visit_one_to_many({vpiParamAssign}, obj_h, shared, [&](AstNode* node) {
                if (node != nullptr) param_map[node->name()] = node;
            });
            (shared.top_nodes)[modType] = module;
            if (v3Global.opt.trace()) { module->modTrace(true); }
            shared.top_param_map[modDefName] = param_map;
        }
        shared.moduleNamesStack.pop();

        // If available, check vpiFullName instead of vpiName, as vpiName can equal vpiDefName
        std::string fullName = objectName;
        if (auto* s = vpi_get_str(vpiFullName, obj_h)) {
            fullName = s;
            sanitize_str(fullName);
        }
        if (fullName != modDefName) {
            // Not a top module, create instance
            AstPin* modPins = nullptr;
            AstPin* modParams = nullptr;

            // Get port assignments
            vpiHandle itr = vpi_iterate(vpiPort, obj_h);
            int np = 0;
            while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
                vpiHandle highConn = vpi_handle(vpiHighConn, vpi_child_obj);
                std::string portName = vpi_get_str(vpiName, vpi_child_obj);
                sanitize_str(portName);
                AstNode* ref = nullptr;
                if (highConn) { ref = visit_object(highConn, shared); }
                AstPin* pin = new AstPin(make_fileline(obj_h), ++np, portName, ref);
                if (!modPins)
                    modPins = pin;
                else
                    modPins->addNextNull(pin);

                vpi_release_handle(vpi_child_obj);
            }
            vpi_release_handle(itr);

            // Get parameter assignments
            itr = vpi_iterate(vpiParamAssign, obj_h);
            std::set<std::string> parameter_set;
            while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
                if(!vpi_get(vpiOverriden, vpi_child_obj)) {
                    // skip parameter assignments with default values
                    continue;
                }

                vpiHandle param_handle = vpi_handle(vpiLhs, vpi_child_obj);
                std::string param_name = get_object_name(param_handle);
                UINFO(3, "Got parameter (pin) " << param_name << std::endl);
                auto is_local = vpi_get(vpiLocalParam, param_handle);
                AstNode* value = nullptr;
                // Try to construct complex expression
                visit_one_to_one({vpiRhs}, vpi_child_obj, shared, [&](AstNode* node) {
                    if (node != nullptr)
                        value = node;
                    else
                        v3error("No value for parameter: " << param_name);
                });
                if (is_local) {
                    // Skip local parameters
                    UINFO(3, "Skipping local parameter (pin) " << param_name << std::endl);
                    continue;
                }
                if (is_imported(param_handle)) {
                    // Skip imported parameters when creating cells
                    UINFO(3, "Skipping imported parameter (pin) " << param_name << std::endl);
                    continue;
                }
                if (parameter_set.find(param_name) == parameter_set.end()) {
                    // Although those are parameters, they are stored as pins
                    AstPin* pin = new AstPin(make_fileline(obj_h), ++np, param_name, value);
                    if (!modParams)
                        modParams = pin;
                    else
                        modParams->addNextNull(pin);
                    parameter_set.insert(param_name);
                } else {
                    // Duplicate
                    UINFO(3, "Duplicate parameter assignment: " << param_name << " in "
                                                                << objectName << std::endl);
                    continue;
                }
                vpi_release_handle(vpi_child_obj);
            }
            vpi_release_handle(itr);
            std::string fullname = get_object_name(obj_h, {vpiFullName});
            UINFO(8, "Adding cell " << fullname << std::endl);
            AstCell* cell = new AstCell(make_fileline(obj_h), make_fileline(obj_h), objectName,
                                        modType, modPins, modParams, nullptr);
            if (v3Global.opt.trace()) { cell->trace(true); }
            return cell;
        }
        break;
    }
    case vpiAssignment:
    case vpiAssignStmt:
    case vpiContAssign: {
        return process_assignment(obj_h, shared);
    }
    case vpiHierPath: {
        return process_hierPath(obj_h, shared);
    }
    case vpiRefVar:
    case vpiRefObj: {
        return get_referenceNode(make_fileline(obj_h), objectName, shared);
    }
    case vpiNetArray: {  // also defined as vpiArrayNet
        // vpiNetArray is used for unpacked arrays
        AstVar* vpi_net = nullptr;
        visit_one_to_many({vpiNet}, obj_h, shared, [&](AstNode* node) {
            if ((node != nullptr) && (vpi_net == nullptr)) {
                vpi_net = reinterpret_cast<AstVar*>(node);
            }
        });

        auto dtypep = getDType(make_fileline(obj_h), obj_h, shared);
        AstVar* v = new AstVar(make_fileline(obj_h), vpi_net->varType(), objectName,
                               VFlagChildDType(), dtypep);
        if (v3Global.opt.trace()) { v->trace(true); }
        return v;
    }

    case vpiEnumNet:
    case vpiStructNet:
    case vpiIntegerNet:
    case vpiTimeNet:
    case vpiPackedArrayNet:
    case vpiLogicNet: {  // also defined as vpiNet
        AstNodeDType* dtype = nullptr;
        auto vpi_net_type = vpi_get(vpiNetType, obj_h);
        AstVarType net_type = AstVarType::UNKNOWN;
        if (vpi_net_type == vpiWire ) {
           net_type = AstVarType::WIRE;
        } else if (vpi_net_type == vpiTri0) {
           net_type = AstVarType::TRI0;
        } else if (vpi_net_type == vpiTri1) {
           net_type = AstVarType::TRI1;
        } else if (vpi_net_type == vpiWand
                   || vpi_net_type == vpiWor
                   || vpi_net_type == vpiTri
                   || vpi_net_type == vpiTriReg
                   || vpi_net_type == vpiTriAnd
                   || vpi_net_type == vpiTriOr ) {
            make_fileline(obj_h)->v3error("Unsupported net type: " << vpi_net_type << std::endl);
        } else {
           net_type = AstVarType::VAR;
        }
        vpiHandle obj_net;
        dtype = getDType(make_fileline(obj_h), obj_h, shared);

        if (net_type == AstVarType::UNKNOWN && dtype == nullptr) {
            // Not set in case above, most likely a "false" port net
            return nullptr;  // Skip this net
        }

        if (objectName == get_object_name(obj_h, {vpiFullName})) {
            size_t pos = objectName.rfind('.');
            objectName = objectName.substr(pos + 1);
        }

        auto* v = new AstVar(make_fileline(obj_h), net_type, objectName, VFlagChildDType(), dtype);
        if (v3Global.opt.trace()) { v->trace(true); }
        return v;
    }
    case vpiStructVar: {
        AstParseRef* refp = getVarRefIfAlreadyDeclared(obj_h, shared);
        if (refp) return refp;

        AstNodeDType* dtypep = getDType(make_fileline(obj_h), obj_h, shared);

        auto* varp = new AstVar(make_fileline(obj_h), AstVarType::VAR, objectName,
                                VFlagChildDType(), dtypep);
        if (v3Global.opt.trace()) { varp->trace(true); }
        visit_one_to_one({vpiExpr}, obj_h, shared, [&](AstNode* itemp) { varp->valuep(itemp); });
        return varp;
    }
    case vpiParameter: {
        return process_parameter(obj_h, shared, true);
    }
    case vpiParamAssign: {
        return process_param_assign(obj_h, shared);
    }
    case vpiInterface: {
        std::string modType = get_object_name(obj_h, {vpiDefName});
        AstIface* interfacep = nullptr;

        // Check if we have encountered this object before
        auto it = shared.top_nodes.find(modType);
        if (it != shared.top_nodes.end()) {
            // Was created before, fill missing
            interfacep = reinterpret_cast<AstIface*>(it->second);
            visit_one_to_many(
                {
                    vpiPort,
                    vpiModport,
                    vpiParamAssign,
                    vpiInterfaceTfDecl,
                    vpiModPath,
                    vpiContAssign,
                    vpiInterface,
                    vpiInterfaceArray,
                    vpiProcess,
                    vpiGenScopeArray,

                    // from vpiInstance
                    vpiProgram,
                    vpiProgramArray,
                    vpiTaskFunc,
                    vpiArrayNet,
                    vpiSpecParam,
                    vpiAssertion,
                    vpiNet,
                    vpiVariables
                },
                obj_h, shared, [&](AstNode* nodep) {
                    if (nodep) { interfacep->addStmtp(nodep); }
                });

            (shared.top_nodes)[modType] = interfacep;
        } else {
            interfacep = new AstIface(make_fileline(obj_h), objectName);

            vpiHandle typedef_itr = vpi_iterate(vpiTypedef, obj_h);
            while (vpiHandle typedef_obj = vpi_scan(typedef_itr)) {
                AstNode* typedefp = process_typedef(typedef_obj, shared);
                if (typedefp != nullptr) interfacep->addStmtp(typedefp);
                vpi_release_handle(typedef_obj);
            }
            vpi_release_handle(typedef_itr);

            visit_one_to_many(
                {
                    vpiContAssign,
                    vpiProcess,
                    vpiTaskFunc,
                },
                obj_h, shared, [&](AstNode* nodep) {
                    if (nodep != nullptr) interfacep->addStmtp(nodep);
                });
            (shared.top_nodes)[modType] = interfacep;
        }

        std::string fullName = get_object_name(obj_h, {vpiFullName, vpiName});
        if (fullName != modType) {
            AstPin* modPins = nullptr;
            vpiHandle itr = vpi_iterate(vpiPort, obj_h);
            int np = 0;
            while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
                vpiHandle highConn = vpi_handle(vpiHighConn, vpi_child_obj);
                if (highConn) {
                    std::string portName = get_object_name(vpi_child_obj);
                    AstParseRef* refp
                        = reinterpret_cast<AstParseRef*>(visit_object(highConn, shared));
                    AstPin* pinp = new AstPin(make_fileline(vpi_child_obj), ++np, portName, refp);
                    if (!modPins)
                        modPins = pinp;
                    else
                        modPins->addNextNull(pinp);
                }

                vpi_release_handle(vpi_child_obj);
            }
            vpi_release_handle(itr);

            AstCell* cellp = new AstCell(make_fileline(obj_h), new FileLine("uhdm"), objectName,
                                         modType, modPins, nullptr, nullptr);
            return cellp;
        }
        break;
    }
    case vpiModport: {
        AstNode* modport_vars = nullptr;

        // We construct a reference here, the net is created in the interface
        // No full visit, just grab name and direction
        auto io_itr = vpi_iterate(vpiIODecl, obj_h);
        while (vpiHandle io_h = vpi_scan(io_itr)) {
            std::string io_name = get_object_name(io_h);
            VDirection dir;
            if (const int n = vpi_get(vpiDirection, io_h)) {
                if (n == vpiInput) {
                    dir = VDirection::INPUT;
                } else if (n == vpiOutput) {
                    dir = VDirection::OUTPUT;
                } else if (n == vpiInout) {
                    dir = VDirection::INOUT;
                }
            }
            auto* io_node = new AstModportVarRef(make_fileline(io_h), io_name, dir);
            if (modport_vars)
                modport_vars->addNextNull(io_node);
            else
                modport_vars = io_node;
            vpi_release_handle(io_h);
        }
        vpi_release_handle(io_itr);

        return new AstModport(make_fileline(obj_h), objectName, modport_vars);
    }
    case vpiIODecl: {
        return process_ioDecl(obj_h, shared);
    }
    case vpiAlways: {
        return process_always(obj_h, shared);
    }
    case vpiEventControl: {
        return process_event_control(obj_h, shared);
    }
    case vpiInitial: {
        AstNode* body = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* node) { body = node; });
        return new AstInitial(make_fileline(obj_h), body);
    }
    case vpiFinal: {
        AstNode* body = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* node) { body = node; });
        return new AstFinal(make_fileline(obj_h), body);
    }
    case vpiNamedBegin:
    case vpiBegin: {
        AstNode* bodyp = process_scope(obj_h, shared);
        visit_one_to_many({vpiStmt}, obj_h, shared, [&](AstNode* nodep) {
            if (bodyp == nullptr) {
                bodyp = nodep;
            } else {
                bodyp->addNextNull(nodep);
            }
        });

        if (objectType == vpiBegin) {
            objectName = "";  // avoid storing parent name
        }
        return new AstBegin(make_fileline(obj_h), objectName, bodyp);
    }
    case vpiNamedFork:
    case vpiFork: {
        if (objectType == vpiFork) {
            objectName = "";  // avoid storing parent name
        }

        AstFork* forkp = new AstFork(make_fileline(obj_h), objectName, nullptr);
        shared.m_symp->pushNew(forkp);

        // vpiJoinType equal to 0 (vpiJoin) is not visible in uhdm tree
        auto join_type = vpi_get(vpiJoinType, obj_h);
        if (join_type == vpiJoin)
            forkp->joinType(VJoinType::JOIN);
        else if (join_type == vpiJoinAny)
            forkp->joinType(VJoinType::JOIN_ANY);
        else if (join_type == vpiJoinNone)
            forkp->joinType(VJoinType::JOIN_NONE);

        AstNode* bodyp = process_scope(obj_h, shared);
        visit_one_to_many({vpiStmt}, obj_h, shared, [&](AstNode* nodep) {
            if (bodyp == nullptr) {
                bodyp = nodep;
            } else {
                bodyp->addNextNull(nodep);
            }
        });
        forkp->addStmtsp(bodyp);

        shared.m_symp->popScope(forkp);
        return forkp;
    }
    case vpiIf:
    case vpiIfElse: {
        AstNode* condition = nullptr;
        AstNode* statement = nullptr;
        AstNode* elseStatement = nullptr;

        visit_one_to_one({vpiCondition}, obj_h, shared, [&](AstNode* node) { condition = node; });
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* node) { statement = node; });
        if (objectType == vpiIfElse) {
            visit_one_to_one({vpiElseStmt}, obj_h, shared,
                             [&](AstNode* node) { elseStatement = node; });
        }
        return new AstIf(make_fileline(obj_h), condition, statement, elseStatement);
    }
    case vpiCase: {
        VCaseType case_type;
        switch (vpi_get(vpiCaseType, obj_h)) {
        case vpiCaseExact: {
            case_type = VCaseType::en::CT_CASE;
            break;
        }
        case vpiCaseX: {
            case_type = VCaseType::en::CT_CASEX;
            break;
        }
        case vpiCaseZ: {
            case_type = VCaseType::en::CT_CASEZ;
            break;
        }
        default: {
            // Should never be reached
            break;
        }
        }
        AstNode* conditionNode = nullptr;
        visit_one_to_one({vpiCondition}, obj_h, shared,
                         [&](AstNode* node) { conditionNode = node; });
        AstNode* itemNodes = nullptr;
        visit_one_to_many({vpiCaseItem}, obj_h, shared, [&](AstNode* item) {
            if (item) {
                if (itemNodes == nullptr) {
                    itemNodes = item;
                } else {
                    itemNodes->addNextNull(item);
                }
            }
        });
        return new AstCase(make_fileline(obj_h), case_type, conditionNode, itemNodes);
    }
    case vpiCaseItem: {
        AstNode* expressionNode = nullptr;
        visit_one_to_many({vpiExpr}, obj_h, shared, [&](AstNode* item) {
            if (item) {
                if (expressionNode == nullptr) {
                    expressionNode = item;
                } else {
                    expressionNode->addNextNull(item);
                }
            }
        });
        AstNode* bodyNode = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* node) { bodyNode = node; });
        return new AstCaseItem(make_fileline(obj_h), expressionNode, bodyNode);
    }
    case vpiOperation: {
        std::vector<AstNode*> operands;
        visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* itemp) {
            if (itemp) { operands.push_back(itemp); }
        });
        return process_operation(obj_h, shared, std::move(operands));
    }
    case vpiTaggedPattern: {
        AstNode* typespecp = nullptr;
        AstNode* patternp = nullptr;
        auto typespec_h = vpi_handle(vpiTypespec, obj_h);
        std::string pattern_name;
        if (auto s = vpi_get_str(vpiName, typespec_h)) {
            pattern_name = s;
            sanitize_str(pattern_name);
            typespecp = new AstText(make_fileline(obj_h), pattern_name);
        } else {
            typespecp = get_value_as_node(typespec_h);
            if (!typespecp)
                v3error("Unable to handle vpiTypespec as constant in vpiTaggedPattern");
        }

        visit_one_to_one({vpiPattern}, obj_h, shared, [&](AstNode* nodep) { patternp = nodep; });
        if (pattern_name == "default") {
            auto* patmp = new AstPatMember(make_fileline(obj_h), patternp, nullptr, nullptr);
            patmp->isDefault(true);
            return patmp;
        } else {
            return new AstPatMember(make_fileline(obj_h), patternp, typespecp, nullptr);
        }
    }
    case vpiEnumConst: {
        return get_value_as_node(obj_h, false);
    }
    case vpiConstant: {
        return get_value_as_node(obj_h, true);
    }
    case vpiBitSelect: {
        objectName = remove_last_sanitized_index(objectName);

        auto* fromp = get_referenceNode(make_fileline(obj_h), objectName, shared);

        AstNode* bitp = nullptr;
        visit_one_to_one({vpiIndex}, obj_h, shared, [&](AstNode* item) {
            if (item) { bitp = item; }
        });

        AstNode* selbitp = new AstSelBit(make_fileline(obj_h), fromp, bitp);

        return selbitp;
    }
    case vpiVarBit:
    case vpiVarSelect: {
        // According to standard, vpiVarBit should be used with packed arrays
        // and vpiVarSelect should be used with unpacked arrays
        // Surelog returns vpiVarSelect in both cases
        // but the fields that we use are the same
        auto* fromp = get_referenceNode(make_fileline(obj_h), objectName, shared);
        AstNode* bitp = nullptr;
        AstNode* selectp = nullptr;
        visit_one_to_many({vpiIndex}, obj_h, shared, [&](AstNode* itemp) {
            bitp = itemp;
            if (itemp->type() == AstType::en::atSelExtract) {
                selectp = new AstSelExtract(make_fileline(obj_h), fromp,
                                            ((AstSelExtract*)itemp)->leftp()->cloneTree(true),
                                            ((AstSelExtract*)itemp)->rightp()->cloneTree(true));
            } else if (itemp->type() == AstType::en::atSelBit) {
                selectp = new AstSelBit(make_fileline(obj_h), fromp,
                                        ((AstSelBit*)itemp)->bitp()->cloneTree(true));
            } else if (itemp->type() == AstType::en::atConst) {
                selectp = new AstSelBit(make_fileline(obj_h), fromp, bitp);
            } else if (itemp->type() == AstType::atSelPlus) {
                AstSelPlus* selplusp = VN_CAST(itemp, SelPlus);
                selectp = new AstSelPlus(make_fileline(obj_h), fromp,
                                         selplusp->bitp()->cloneTree(true),
                                         selplusp->widthp()->cloneTree(true));
            } else if (itemp->type() == AstType::atSelMinus) {
                AstSelMinus* selminusp = VN_CAST(itemp, SelMinus);
                selectp = new AstSelMinus(make_fileline(obj_h), fromp,
                                          selminusp->bitp()->cloneTree(true),
                                          selminusp->widthp()->cloneTree(true));

            } else {
                selectp = new AstSelBit(make_fileline(obj_h), fromp, bitp);
            }
            fromp = selectp;
        });
        return selectp;
    }
    case vpiTask:
    case vpiFunction: {
        return process_function_task(obj_h, shared);
    }
    case vpiReturn:
    case vpiReturnStmt: {
        AstNode* conditionp = nullptr;
        visit_one_to_one({vpiCondition}, obj_h, shared, [&](AstNode* itemp) {
            if (itemp) { conditionp = itemp; }
        });
        if (conditionp) {
            return new AstReturn(make_fileline(obj_h), conditionp);
        } else {
            return new AstReturn(make_fileline(obj_h));
        }
    }
    case vpiTaskCall:
    case vpiFuncCall: {
        AstNode* func_task_refp = nullptr;
        AstNode* arguments = nullptr;
        visit_one_to_many({vpiArgument}, obj_h, shared, [&](AstNode* item) {
            if (item) {
                if (arguments == nullptr) {
                    arguments = new AstArg(make_fileline(obj_h), "", item);
                } else {
                    arguments->addNextNull(new AstArg(make_fileline(obj_h), "", item));
                }
            }
        });
        AstNode* refp = get_class_package_ref_node(make_fileline(obj_h), objectName, shared);
        size_t colon_pos = objectName.rfind("::");
        if (colon_pos != std::string::npos) objectName = objectName.substr(colon_pos + 2);

        size_t dot_pos = objectName.rfind('.');
        if (dot_pos != std::string::npos) {
            // Split object name into prefix.method
            // TODO: Handle >1 dot, currently all goes into prefix
            std::string lhs = objectName.substr(0, dot_pos);
            std::string rhs = objectName.substr(dot_pos + 1, objectName.length());
            AstNode* from = get_referenceNode(make_fileline(obj_h), lhs, shared);
            func_task_refp = new AstMethodCall(make_fileline(obj_h), from, rhs, arguments);
        } else {
            // Functions can be called as tasks, depending on context
            bool inExpression = is_expr_context(obj_h);

            if (inExpression)
                func_task_refp = new AstFuncRef(make_fileline(obj_h), objectName, arguments);
            else
                func_task_refp = new AstTaskRef(make_fileline(obj_h), objectName, arguments);
        }

        return AstDot::newIfPkg(make_fileline(obj_h), refp, func_task_refp);
    }
    case vpiSysFuncCall: {
        std::vector<AstNode*> arguments;
        visit_one_to_many({vpiArgument}, obj_h, shared, [&](AstNode* item) {
            if (item) { arguments.push_back(item); }
        });

        #define VL_SIMPLE_SYSFUNC_CALL(taskName, astName, ...) { \
            #taskName, /* task name as map key */ \
            [](auto obj_h, auto& shared, auto& args) { \
                auto* fl = make_fileline(obj_h); \
                return new Ast##astName(fl, __VA_ARGS__); \
            } \
        }
        #define VL_SYSFUNC_CALL(taskName, body) { \
            #taskName, /* task name as map key */ \
            [](auto obj_h, auto& shared, auto& args) { \
                auto* fl = make_fileline(obj_h); \
                body \
            } \
        }
        using SysFuncCallMaker = std::function<AstNode*(vpiHandle, UhdmShared&, std::vector<AstNode*>&)>;
        static const std::unordered_map<std::string, SysFuncCallMaker> sysFuncCallMakers = {
            VL_SIMPLE_SYSFUNC_CALL($acos, AcosD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($acosh, AcoshD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($asin, AsinD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($asinh, AsinhD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($atan, AtanD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($atan2, Atan2D, args[0], args[1]),
            VL_SIMPLE_SYSFUNC_CALL($atanh, AtanhD, args[0]),
            VL_SYSFUNC_CALL($bits, {
                        // Verilator's original parser allow $bits function to have 2 arguments
                        // but it is not defined in standard
                        if (args.size() != 1)
                            fl->v3error("Number of arguments is not 1");
                        vpiHandle arg_itr = vpi_iterate(vpiArgument, obj_h);
                        vpiHandle arg_h = vpi_scan(arg_itr);
                        AstNode* expr_datatype_p = nullptr;
                        // Check if it is type/variable name or expression
                        const unsigned int objectType = vpi_get(vpiType, arg_h);
                        if (objectType == vpiRefObj) {
                            // In case of funtion arguments Surelog parses
                            // both type names and variable names as vpiRefObjs
                            // We check if vpiActual field exists.
                            // If so, we assume that the argument is variable name
                            std::string argumentName = get_object_name(arg_h);
                            if (vpiHandle actual_h = vpi_handle(vpiActual, arg_h)) {
                                expr_datatype_p = new AstParseRef(make_fileline(arg_h), VParseRefExp::en::PX_TEXT,
                                                                  argumentName);
                                vpi_release_handle(actual_h);
                            } else {
                                expr_datatype_p = new AstRefDType(make_fileline(arg_h), argumentName);
                            }
                        } else {
                            expr_datatype_p = args[0];
                        }
                        vpi_release_handle(arg_itr);
                        vpi_release_handle(arg_h);
                        return new AstAttrOf(make_fileline(obj_h), AstAttrType::DIM_BITS, expr_datatype_p);
                    }),
            VL_SIMPLE_SYSFUNC_CALL($bitstoreal, BitsToRealD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($ceil, CeilD, args[0]),
            VL_SYSFUNC_CALL($changed, {
                    if (args.size() > 1) fl->v3warn(E_UNSUPPORTED, "Unsupported: $changed and clock arguments");
                    return new AstLogNot(fl, new AstStable(fl, args[0]));
                }),
            VL_SIMPLE_SYSFUNC_CALL($clog2, CLog2, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($cos, CosD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($cosh, CoshD, args[0]),
            VL_SYSFUNC_CALL($countbits, {
                    if (args.size() > 3) return new AstCountBits(fl, args[0], args[1], args[2], args[3]);
                    else if (args.size() > 2) return new AstCountBits(fl, args[0], args[1], args[2]);
                    else return new AstCountBits(fl, args[0], args[1]);
                }),
            VL_SIMPLE_SYSFUNC_CALL($countones, CountOnes, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($dimensions, AttrOf, AstAttrType::DIM_DIMENSIONS, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($exp, ExpD, args[0]),
            VL_SYSFUNC_CALL($fell, {
                    if (args.size() > 1) fl->v3warn(E_UNSUPPORTED, "Unsupported: $fell and clock arguments");
                    return new AstFell(fl, args[0]);
                }),
            VL_SIMPLE_SYSFUNC_CALL($feof, FEof, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($ferror, FError, args[0], args[1]),
            VL_SIMPLE_SYSFUNC_CALL($fgetc, FGetC, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($fgets, FGetS, args[0], args[1]),
            VL_SIMPLE_SYSFUNC_CALL($fread, FRead, args[0], args[1], args.size() > 2 ? args[2] : nullptr, args.size() > 3 ? args[3] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($frewind, FRewind, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($floor, FloorD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($fseek, FSeek, args[0], args[1], args[2]),
            VL_SIMPLE_SYSFUNC_CALL($ftell, FTell, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($high, AttrOf, AstAttrType::DIM_HIGH, args[0], args.size() > 1 ? args[1] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($hypot, HypotD, args[0], args[1]),
            VL_SIMPLE_SYSFUNC_CALL($increment, AttrOf, AstAttrType::DIM_INCREMENT, args[0], args.size() > 1 ? args[1] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($isunbounded, IsUnbounded, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($isunknown, IsUnknown, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($itor, IToRD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($left, AttrOf, AstAttrType::DIM_LEFT, args[0], args.size() > 1 ? args[1] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($ln, LogD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($log10, Log10D, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($low, AttrOf, AstAttrType::DIM_LOW, args[0], args.size() > 1 ? args[1] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($onehot, OneHot, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($onehot0, OneHot0, args[0]),
            VL_SYSFUNC_CALL($past, {
                    if (args.size() > 2) fl->v3warn(E_UNSUPPORTED, "Unsupported: $past expr2 and clock arguments");
                    return new AstPast(fl, args[0], args.size() > 1 ? args[1] : nullptr);
                }),
            VL_SIMPLE_SYSFUNC_CALL($pow, PowD, args[0], args[1]),
            VL_SIMPLE_SYSFUNC_CALL($random, Rand, args.empty() ? nullptr : args[0], false),
            VL_SIMPLE_SYSFUNC_CALL($realtime, TimeD, VTimescale::NONE),
            VL_SIMPLE_SYSFUNC_CALL($realtobits, RealToBits, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($rewind, FSeek, args[0], new AstConst(fl, 0), new AstConst(fl, 0)),
            VL_SIMPLE_SYSFUNC_CALL($right, AttrOf, AstAttrType::DIM_RIGHT, args[0], args.size() > 1 ? args[1] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($rose, Rose, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($rtoi, RToIS, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($sampled, Sampled, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($sformat, SFormat, args[0], vectorToAstList(args.begin() + 1, args.end())),
            VL_SIMPLE_SYSFUNC_CALL($sformatf, SFormatF, AstSFormatF::NoFormat(), vectorToAstList(args)),
            VL_SIMPLE_SYSFUNC_CALL($signed, Signed, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($sin, SinD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($sinh, SinhD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($size, AttrOf, AstAttrType::DIM_SIZE, args[0], args.size() > 1 ? args[1] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($sqrt, SqrtD, args[0]),
            VL_SYSFUNC_CALL($stable, {
                    if (args.size() > 1) fl->v3warn(E_UNSUPPORTED, "Unsupported: $stable and clock arguments");
                    return new AstStable(fl, args[0]);
                }),
            VL_SIMPLE_SYSFUNC_CALL($stime, Sel, new AstTime(fl, VTimescale(VTimescale::NONE)), 0, 32),
            VL_SIMPLE_SYSFUNC_CALL($tan, TanD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($tanh, TanhD, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($time, Time, VTimescale(VTimescale::NONE)),
            VL_SIMPLE_SYSFUNC_CALL($typename, AttrOf, AstAttrType::TYPENAME, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($ungetc, FUngetC, args[1], args[0]),
            VL_SIMPLE_SYSFUNC_CALL($unpacked_dimensions, AttrOf, AstAttrType::DIM_UNPK_DIMENSIONS, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($unsigned, Unsigned, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($urandom, Rand, args.empty()? nullptr : args[0], true),
            VL_SIMPLE_SYSFUNC_CALL($urandom_range, URandomRange, args[0], args.size() > 1 ? args[1] : new AstConst(fl, 0)),
            VL_SIMPLE_SYSFUNC_CALL($value$plusargs, ValuePlusArgs, args[0], args[1]),

            VL_SIMPLE_SYSFUNC_CALL($dumpports, DumpCtl, VDumpCtlType::FILE, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($dumpfile, DumpCtl, VDumpCtlType::FILE, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($dumpvars, DumpCtl, VDumpCtlType::VARS, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($dumpall, DumpCtl, VDumpCtlType::ALL),
            VL_SIMPLE_SYSFUNC_CALL($dumpflush, DumpCtl, VDumpCtlType::FLUSH),
            VL_SIMPLE_SYSFUNC_CALL($dumplimit, DumpCtl, VDumpCtlType::LIMIT, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($dumpoff, DumpCtl, VDumpCtlType::OFF),
            VL_SIMPLE_SYSFUNC_CALL($dumpon, DumpCtl, VDumpCtlType::ON),
            VL_SIMPLE_SYSFUNC_CALL($system, SystemT, args[0]),
            VL_SYSFUNC_CALL($exit, { return new AstFinish(fl); }),
            VL_SIMPLE_SYSFUNC_CALL($fclose, FClose, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($fflush, FFlush, nullptr),
            VL_SYSFUNC_CALL($finish, { return new AstFinish(fl); }),
            VL_SIMPLE_SYSFUNC_CALL($stop, Stop, false),
            VL_SIMPLE_SYSFUNC_CALL($sformat, SFormat, args[0], args[1]),
            VL_SIMPLE_SYSFUNC_CALL($swrite, SFormat, args[0], args[1]),
            VL_SIMPLE_SYSFUNC_CALL($swriteb, SFormat, args[0], args[1], 'b'),
            VL_SIMPLE_SYSFUNC_CALL($swriteh, SFormat, args[0], args[1], 'h'),
            VL_SIMPLE_SYSFUNC_CALL($swriteo, SFormat, args[0], args[1], 'o'),
            VL_SIMPLE_SYSFUNC_CALL($display, Display, AstDisplayType::DT_DISPLAY, nullptr, vectorToAstList(args)),
            VL_SIMPLE_SYSFUNC_CALL($displayb, Display, AstDisplayType::DT_DISPLAY, nullptr, vectorToAstList(args), 'b'),
            VL_SIMPLE_SYSFUNC_CALL($displayh, Display, AstDisplayType::DT_DISPLAY, nullptr, vectorToAstList(args), 'h'),
            VL_SIMPLE_SYSFUNC_CALL($displayo, Display, AstDisplayType::DT_DISPLAY, nullptr, vectorToAstList(args), 'o'),
            VL_SIMPLE_SYSFUNC_CALL($monitor, Display, AstDisplayType::DT_MONITOR, nullptr, vectorToAstList(args)),
            VL_SIMPLE_SYSFUNC_CALL($monitorb, Display, AstDisplayType::DT_MONITOR, nullptr, vectorToAstList(args), 'b'),
            VL_SIMPLE_SYSFUNC_CALL($monitorh, Display, AstDisplayType::DT_MONITOR, nullptr, vectorToAstList(args), 'h'),
            VL_SIMPLE_SYSFUNC_CALL($monitoro, Display, AstDisplayType::DT_MONITOR, nullptr, vectorToAstList(args), 'o'),
            VL_SIMPLE_SYSFUNC_CALL($strobe, Display, AstDisplayType::DT_STROBE, nullptr, vectorToAstList(args)),
            VL_SIMPLE_SYSFUNC_CALL($strobeb, Display, AstDisplayType::DT_STROBE, nullptr, vectorToAstList(args), 'b'),
            VL_SIMPLE_SYSFUNC_CALL($strobeh, Display, AstDisplayType::DT_STROBE, nullptr, vectorToAstList(args), 'h'),
            VL_SIMPLE_SYSFUNC_CALL($strobeo, Display, AstDisplayType::DT_STROBE, nullptr, vectorToAstList(args), 'o'),
            VL_SIMPLE_SYSFUNC_CALL($write, Display, AstDisplayType::DT_WRITE, nullptr, vectorToAstList(args)),
            VL_SIMPLE_SYSFUNC_CALL($writeb, Display, AstDisplayType::DT_WRITE, nullptr, vectorToAstList(args), 'b'),
            VL_SIMPLE_SYSFUNC_CALL($writeh, Display, AstDisplayType::DT_WRITE, nullptr, vectorToAstList(args), 'h'),
            VL_SIMPLE_SYSFUNC_CALL($writeo, Display, AstDisplayType::DT_WRITE, nullptr, vectorToAstList(args), 'o'),
            VL_SIMPLE_SYSFUNC_CALL($fdisplay, Display, AstDisplayType::DT_DISPLAY, args[0], vectorToAstList(args.begin() + 1, args.end())),
            VL_SIMPLE_SYSFUNC_CALL($fdisplayb, Display, AstDisplayType::DT_DISPLAY, args[0], vectorToAstList(args.begin() + 1, args.end()), 'b'),
            VL_SIMPLE_SYSFUNC_CALL($fdisplayh, Display, AstDisplayType::DT_DISPLAY, args[0], vectorToAstList(args.begin() + 1, args.end()), 'h'),
            VL_SIMPLE_SYSFUNC_CALL($fdisplayo, Display, AstDisplayType::DT_DISPLAY, args[0], vectorToAstList(args.begin() + 1, args.end()), 'o'),
            VL_SIMPLE_SYSFUNC_CALL($fmonitor, Display, AstDisplayType::DT_MONITOR, args[0], vectorToAstList(args.begin() + 1, args.end())),
            VL_SIMPLE_SYSFUNC_CALL($fmonitorb, Display, AstDisplayType::DT_MONITOR, args[0], vectorToAstList(args.begin() + 1, args.end()), 'b'),
            VL_SIMPLE_SYSFUNC_CALL($fmonitorh, Display, AstDisplayType::DT_MONITOR, args[0], vectorToAstList(args.begin() + 1, args.end()), 'h'),
            VL_SIMPLE_SYSFUNC_CALL($fmonitoro, Display, AstDisplayType::DT_MONITOR, args[0], vectorToAstList(args.begin() + 1, args.end()), 'o'),
            VL_SIMPLE_SYSFUNC_CALL($fstrobe, Display, AstDisplayType::DT_STROBE, args[0], vectorToAstList(args.begin() + 1, args.end())),
            VL_SIMPLE_SYSFUNC_CALL($fstrobeb, Display, AstDisplayType::DT_STROBE, args[0], vectorToAstList(args.begin() + 1, args.end()), 'b'),
            VL_SIMPLE_SYSFUNC_CALL($fstrobeh, Display, AstDisplayType::DT_STROBE, args[0], vectorToAstList(args.begin() + 1, args.end()), 'h'),
            VL_SIMPLE_SYSFUNC_CALL($fstrobeo, Display, AstDisplayType::DT_STROBE, args[0], vectorToAstList(args.begin() + 1, args.end()), 'o'),
            VL_SIMPLE_SYSFUNC_CALL($fwrite, Display, AstDisplayType::DT_WRITE, args[0], vectorToAstList(args.begin() + 1, args.end())),
            VL_SIMPLE_SYSFUNC_CALL($fwriteb, Display, AstDisplayType::DT_WRITE, args[0], vectorToAstList(args.begin() + 1, args.end()), 'b'),
            VL_SIMPLE_SYSFUNC_CALL($fwriteh, Display, AstDisplayType::DT_WRITE, args[0], vectorToAstList(args.begin() + 1, args.end()), 'h'),
            VL_SIMPLE_SYSFUNC_CALL($fwriteo, Display, AstDisplayType::DT_WRITE, args[0], vectorToAstList(args.begin() + 1, args.end()), 'o'),
            VL_SIMPLE_SYSFUNC_CALL($info, Display, AstDisplayType::DT_INFO, nullptr, args[0]),
            VL_SIMPLE_SYSFUNC_CALL($warning, Display, AstDisplayType::DT_WARNING, nullptr, args[0]),
            VL_SYSFUNC_CALL($error, {
                    auto* displayp = new AstDisplay(fl, AstDisplayType::DT_ERROR, nullptr, vectorToAstList(args));
                    displayp->addNext(new AstStop(fl, true));
                    return displayp;
                }),
            VL_SYSFUNC_CALL($fatal, {
                    auto* displayp = new AstDisplay(fl, AstDisplayType::DT_FATAL, nullptr, vectorToAstList(args));
                    displayp->addNext(new AstStop(fl, false));
                    return displayp;
                }),
            VL_SIMPLE_SYSFUNC_CALL($monitoroff, MonitorOff, true),
            VL_SIMPLE_SYSFUNC_CALL($monitoron, MonitorOff, false),
            VL_SYSFUNC_CALL($printtimescale, { return new AstPrintTimeScale(fl); }),
            VL_SIMPLE_SYSFUNC_CALL($timeformat, TimeFormat, args[0], args[1], args[2], args[3]),
            VL_SIMPLE_SYSFUNC_CALL($readmemb, ReadMem, false, args[0], args[1], args.size() > 2 ? args[2] : nullptr, args.size() > 3 ? args[3] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($readmemh, ReadMem, true, args[0], args[1], args.size() > 2 ? args[2] : nullptr, args.size() > 3 ? args[3] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($writememb, WriteMem, false, args[0], args[1], args.size() > 2 ? args[2] : nullptr, args.size() > 3 ? args[3] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($writememh, WriteMem, true, args[0], args[1], args.size() > 2 ? args[2] : nullptr, args.size() > 3 ? args[3] : nullptr),
            VL_SIMPLE_SYSFUNC_CALL($cast, CastParse, args[0], args[1]),

            VL_SYSFUNC_CALL($fopen, {
                    auto parent_h = vpi_handle({vpiParent}, obj_h);
                    auto lhs_h = vpi_handle({vpiLhs}, parent_h);
                    AstNode* fd = nullptr;
                    if (lhs_h) { fd = visit_object(lhs_h, shared); }
                    return new AstFOpen(make_fileline(obj_h), fd, args[0], args[1]);
                }),
            VL_SYSFUNC_CALL($__BAD_SYMBOL__, {
                    fl->v3info("Bad symbol encountered!");
                    // Dummy statement to keep parsing
                    return new AstTime(make_fileline(obj_h), VTimescale::NONE);
                })
        };
        auto it = sysFuncCallMakers.find(objectName);
        if (it != sysFuncCallMakers.end())
            node = it->second(obj_h, shared, arguments);
        else
            v3error("\t! Encountered unhandled SysFuncCall: " << objectName);
        if (VN_IS(node, NodeMath) && !VN_IS(node, Signed) && !VN_IS(node, Unsigned)) {
            auto parent_h = vpi_handle(vpiParent, obj_h);
            int parent_type = 0;
            if (parent_h) {
                parent_type = vpi_get(vpiType, parent_h);
                vpi_release_handle(parent_h);
                if (parent_type == vpiBegin) {  // TODO: Are other contexts missing here?
                    // Intask-like context return values are discarded
                    // This is indicated by wrapping the node
                    return new AstSysFuncAsTask(make_fileline(obj_h), node);
                }
            }
        }
        return node;
    }
    case vpiRange: {
        AstNode* msbNode = nullptr;
        AstNode* lsbNode = nullptr;
        AstRange* rangeNode = nullptr;
        auto leftRange_h = vpi_handle(vpiLeftRange, obj_h);
        if (leftRange_h) { msbNode = visit_object(leftRange_h, shared); }
        auto rightRange_h = vpi_handle(vpiRightRange, obj_h);
        if (rightRange_h) { lsbNode = visit_object(rightRange_h, shared); }
        if (msbNode && lsbNode) {
            rangeNode = new AstRange(make_fileline(obj_h), msbNode, lsbNode);
        }
        return rangeNode;
    }
    case vpiPartSelect: {
        AstNode* msbNode = nullptr;
        AstNode* lsbNode = nullptr;
        AstNode* fromNode = nullptr;

        visit_one_to_one(
            {
                vpiLeftRange,
                vpiRightRange,
            },
            obj_h, shared, [&](AstNode* item) {
                if (item) {
                    if (msbNode == nullptr) {
                        msbNode = item;
                    } else if (lsbNode == nullptr) {
                        lsbNode = item;
                    }
                }
            });
        auto parent_h = vpi_handle(vpiParent, obj_h);
        if (parent_h != 0) {
            std::string parent_name = get_object_name(parent_h, {vpiName, vpiFullName});

            fromNode = get_referenceNode(make_fileline(obj_h), parent_name, shared);
        }
        return new AstSelExtract(make_fileline(obj_h), fromNode, msbNode, lsbNode);
    }
    case vpiIndexedPartSelect: {
        AstNode* bit = nullptr;
        AstNode* width = nullptr;
        AstNode* fromNode = nullptr;

        visit_one_to_one(
            {
                vpiBaseExpr,
                vpiWidthExpr,
            },
            obj_h, shared, [&](AstNode* item) {
                if (item) {
                    if (bit == nullptr) {
                        bit = item;
                    } else if (width == nullptr) {
                        width = item;
                    }
                }
            });
        auto parent_h = vpi_handle(vpiParent, obj_h);
        std::string parent_name = get_object_name(parent_h, {vpiName, vpiFullName});

        fromNode = get_referenceNode(make_fileline(obj_h), parent_name, shared);

        auto type = vpi_get(vpiIndexedPartSelectType, obj_h);
        if (type == vpiPosIndexed) {
            return new AstSelPlus(make_fileline(obj_h), fromNode, bit, width);
        } else if (type == vpiNegIndexed) {
            return new AstSelMinus(make_fileline(obj_h), fromNode, bit, width);
        } else {
            return nullptr;
        }
    }
    case vpiFor: {
        AstNode* initsp = nullptr;
        AstNode* condp = nullptr;
        AstNode* incsp = nullptr;
        AstNode* bodysp = nullptr;
        visit_one_to_one(
            {
                vpiForInitStmt,
            },
            obj_h, shared, [&](AstNode* item) { initsp = item; });
        visit_one_to_many(
            {
                vpiForInitStmt,
            },
            obj_h, shared, [&](AstNode* item) {
                if (initsp == nullptr) {
                    initsp = item;
                } else {
                    initsp->addNextNull(item);
                }
            });
        visit_one_to_one(
            {
                vpiCondition,
            },
            obj_h, shared, [&](AstNode* item) {
                if (condp == nullptr) {
                    condp = item;
                } else {
                    condp->addNextNull(item);
                }
            });
        visit_one_to_one(
            {
                vpiForIncStmt,
            },
            obj_h, shared, [&](AstNode* item) { incsp = item; });
        visit_one_to_many(
            {
                vpiForIncStmt,
            },
            obj_h, shared, [&](AstNode* item) {
                if (incsp == nullptr) {
                    incsp = item;
                } else {
                    incsp->addNextNull(item);
                }
            });
        visit_one_to_one(
            {
                vpiStmt,
            },
            obj_h, shared, [&](AstNode* item) {
                if (bodysp == nullptr) {
                    bodysp = item;
                } else {
                    bodysp->addNextNull(item);
                }
            });
        AstNode* loop = new AstWhile(make_fileline(obj_h), condp, bodysp, incsp);
        initsp->addNextNull(loop);
        AstNode* stmt = new AstBegin(make_fileline(obj_h), "", initsp);
        return stmt;
    }
    case vpiRepeat:
    case vpiDoWhile:
    case vpiWhile: {
        AstNode* condp = nullptr;
        AstNode* bodysp = nullptr;
        visit_one_to_one(
            {
                vpiCondition,
            },
            obj_h, shared, [&](AstNode* itemp) {
                    condp = itemp;
            });
        visit_one_to_one(
            {
                vpiStmt,
            },
            obj_h, shared, [&](AstNode* itemp) {
                    bodysp = itemp;
            });

        if (objectType == vpiRepeat)
            return new AstRepeat(make_fileline(obj_h), condp, bodysp);
        else if (objectType == vpiWhile)
            return new AstWhile(make_fileline(obj_h), condp, bodysp);
        else if (objectType == vpiDoWhile) {
            AstWhile* loopp = new AstWhile(make_fileline(obj_h), condp, bodysp);
            auto* firstIterp = bodysp->cloneTree(true);
            firstIterp->addNext(loopp);
            return firstIterp;
        }
        break;
    }

    case vpiBitTypespec:
    case vpiLogicTypespec:
    case vpiIntTypespec:
    case vpiStringTypespec:
    case vpiChandleTypespec:
    case vpiIntegerTypespec:
    case vpiVoidTypespec:
    case vpiEnumTypespec:
    case vpiStructTypespec:
    case vpiPackedArrayTypespec:
    case vpiUnsupportedTypespec: {
        return process_typespec(obj_h, shared);
    }
    case vpiTypespecMember: {
        return process_typespec_member(obj_h, shared);
    }
    case vpiTypeParameter: {
        vpiHandle typespec_h = vpi_handle(vpiTypespec, obj_h);
        return process_typespec(typespec_h, shared);
    }
    case vpiLogicVar:
    case vpiStringVar:
    case vpiTimeVar:
    case vpiRealVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiIntegerVar:
    case vpiShortIntVar:
    case vpiShortRealVar:
    case vpiEnumVar:
    case vpiBitVar:
    case vpiByteVar: {
        AstParseRef* refp = getVarRefIfAlreadyDeclared(obj_h, shared);
        if (refp) return refp;

        AstNodeDType* dtype = getDType(make_fileline(obj_h), obj_h, shared);
        auto* var = new AstVar(make_fileline(obj_h), AstVarType::VAR, objectName,
                               VFlagChildDType(), dtype);
        if (v3Global.opt.trace()) { var->trace(true); }
        visit_one_to_one({vpiExpr}, obj_h, shared, [&](AstNode* item) { var->valuep(item); });
        return var;
    }
    case vpiPackedArrayVar:
    case vpiArrayVar: {
        AstParseRef* refp = getVarRefIfAlreadyDeclared(obj_h, shared);
        if (refp) return refp;

        auto dtypep = getDType(make_fileline(obj_h), obj_h, shared);

        auto* varp = new AstVar(make_fileline(obj_h), AstVarType::VAR, objectName,
                                VFlagChildDType(), dtypep);
        visit_one_to_one({vpiExpr}, obj_h, shared, [&](AstNode* itemp) { varp->valuep(itemp); });

        if (objectType == vpiPackedArrayVar) {
            int elements_count = 0;
            vpiHandle element_itr = vpi_iterate(vpiElement, obj_h);
            // It looks like Surelog returns at most 1 vpiElement node
            // Elements of the array are given as operation vpiExpr of vpiElement
            while (vpiHandle element_h = vpi_scan(element_itr)) {
                elements_count++;
                if (elements_count > 1) v3error("vpiPackedArray has more than 1 vpiElement nodes");
                if (varp->valuep()) {
                    UINFO(7, "vpiPackedArray has both vpiElement and vpiExpr node, taking vpiExpr as value"
                          << std::endl);
                    break;
                }

                visit_one_to_one({vpiExpr}, element_h, shared,
                                 [&](AstNode* itemp) { varp->valuep(itemp); });
                vpi_release_handle(element_h);
            }
            vpi_release_handle(element_itr);
        }

        if (v3Global.opt.trace()) { varp->trace(true); }
        return varp;
    }
    case vpiChandleVar: {
        AstParseRef* refp = getVarRefIfAlreadyDeclared(obj_h, shared);
        if (refp) return refp;

        auto* dtype = new AstBasicDType(make_fileline(obj_h), AstBasicDTypeKwd::CHANDLE);
        auto* var = new AstVar(make_fileline(obj_h), AstVarType::VAR, objectName,
                               VFlagChildDType(), dtype);
        if (v3Global.opt.trace()) { var->trace(true); }
        return var;
    }
    case vpiGenScopeArray: {
        return process_genScopeArray(obj_h, shared);
    }
    case vpiGenScope: {
        AstNode* statementsp = nullptr;

        vpiHandle typedef_itr = vpi_iterate(vpiTypedef, obj_h);
        while (vpiHandle typedef_h = vpi_scan(typedef_itr)) {
            AstNode* typedefp = process_typedef(typedef_h, shared);
            if (statementsp == nullptr)
                statementsp = typedefp;
            else
                statementsp->addNextNull(typedefp);

            vpi_release_handle(typedef_h);
        }
        vpi_release_handle(typedef_itr);

        // Due to problems with sizes of constants,
        // vpiParameter node should only be handled when there is no vpiParamAssign node
        // corresponding to this parameter
        // https://github.com/chipsalliance/Surelog/issues/2107#issuecomment-951025142

        std::set<std::string> param_assign_names;
        visit_one_to_many({vpiParamAssign}, obj_h, shared, [&](AstNode* nodep) {
            param_assign_names.insert(nodep->name());
            if (statementsp == nullptr)
                statementsp = nodep;
            else
                statementsp->addNextNull(nodep);
        });

        vpiHandle parameter_itr = vpi_iterate(vpiParameter, obj_h);
        while (vpiHandle parameter_h = vpi_scan(parameter_itr)) {
            std::string parameter_name = vpi_get_str(vpiName, parameter_h);
            if (param_assign_names.find(parameter_name) == param_assign_names.end()) {
                AstNode* parameterp = process_parameter(parameter_h, shared, true);
                if (statementsp == nullptr)
                    statementsp = parameterp;
                else
                    statementsp->addNextNull(parameterp);
            }
            vpi_release_handle(parameter_h);
        }
        vpi_release_handle(parameter_itr);

        visit_one_to_many(
            {
                vpiInternalScope,
                vpiArrayNet,
                // vpiLogicVar,
                // vpiArrayVar,
                vpiMemory,
                vpiVariables,
                vpiNet,
                vpiNamedEvent,
                vpiNamedEventArray,
                vpiProcess,
                vpiContAssign,
                vpiModule,
                vpiModuleArray,
                vpiPrimitive,
                vpiPrimitiveArray,
                vpiDefParam,
                vpiGenScopeArray,
                vpiProgram,
                vpiProgramArray,
                // vpiAssertion,
                vpiInterface,
                vpiInterfaceArray,
                vpiAliasStmt,
                vpiClockingBlock,
            },
            obj_h, shared, [&](AstNode* itemp) {
                if (statementsp == nullptr) {
                    statementsp = itemp;
                } else {
                    statementsp->addNextNull(itemp);
                }
            });
        return statementsp;
    }
    case vpiDelayControl: {
        s_vpi_delay delay;
        vpi_get_delays(obj_h, &delay);

        // Verilator ignores delay statements, just grab the first one for simplicity
        if (delay.da != nullptr) {
            auto* delay_c = new AstConst(make_fileline(obj_h), delay.da[0].real);
            return new AstDelay(make_fileline(obj_h), delay_c);
        }
    }
    case vpiBreak: {
        return new AstBreak(make_fileline(obj_h));
    }
    case vpiContinue: {
        return new AstContinue(make_fileline(obj_h));
    }
    case vpiForeachStmt: {
        AstNode* arrayp = nullptr;  // Array, then index variables
        AstNode* bodyp = nullptr;
        visit_one_to_one({vpiVariables}, obj_h, shared, [&](AstNode* item) {
            if (arrayp == nullptr) {
                arrayp = item;
            } else {
                arrayp->addNextNull(item);
            }
        });
        visit_one_to_many({vpiLoopVars}, obj_h, shared, [&](AstNode* item) {
            if (arrayp == nullptr) {
                arrayp = item;
            } else {
                arrayp->addNextNull(item);
            }
        });
        visit_one_to_many({vpiStmt}, obj_h, shared, [&](AstNode* item) {
            if (bodyp == nullptr) {
                bodyp = item;
            } else {
                bodyp->addNextNull(item);
            }
        });
        return new AstForeach(make_fileline(obj_h), arrayp, bodyp);
    }
    case vpiForever: {
        AstNode* bodyp = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* itemp) {
            bodyp = itemp;
        });
        return new AstWhile(make_fileline(obj_h),
                            new AstConst(make_fileline(obj_h), AstConst::BitTrue()),
                            bodyp);
    }
    case vpiDisable: {
        FileLine* fl = make_fileline(obj_h);
        if (vpiHandle expr_h = vpi_handle(vpiExpr, obj_h)) {
            std::string scopeName = get_object_name(expr_h);
            vpi_release_handle(expr_h);
            return new AstDisable(fl, scopeName);
        } else {
            fl->v3error("No vpiExpr of vpiDisable, required to get the name of the disabled object");
            return nullptr;
        }
    }
    case vpiMethodFuncCall: {
        return process_method_call(obj_h, nullptr, shared);
    }
    // What we can see (but don't support yet)
    case vpiClassObj: break;
    case vpiClassDefn: {
        auto* definition = new AstClass(make_fileline(obj_h), objectName);
        visit_one_to_many(
            {
                vpiVariables,
                // vpiMethods,  // Not supported yet in UHDM
                vpiConstraint,
                vpiParamAssign,
                vpiNamedEvent,
                vpiNamedEventArray,
                vpiInternalScope,
            },
            obj_h, shared, [&](AstNode* item) {
                if (item != nullptr) { definition->addMembersp(item); }
            });
        return definition;
    }
    case vpiImmediateAssert: {
        AstAssert* assert = nullptr;
        visit_one_to_one({vpiExpr}, obj_h, shared, [&](AstNode* item) {
            if (item != nullptr) {
                assert = new AstAssert(make_fileline(obj_h), item, nullptr, nullptr, true);
            }
        });
        return assert;
    }
    case vpiUnsupportedStmt: {
        auto* fl = make_fileline(obj_h);
        fl->v3error("\t! This statement is unsupported in UHDM: " << file_name << ":" << currentLine);
        break;
    }
    case vpiUnsupportedExpr: {
        auto* fl = make_fileline(obj_h);
        // Note: this can also happen if Surelog could not resolve a type
        fl->v3error("\t! This expression is unsupported in UHDM: " << file_name << ":" << currentLine);
        break;
    }
    default: {
        // Notify we have something unhandled
        auto* fl = make_fileline(obj_h);
        fl->v3error("\t! Unhandled type: " << objectType << ":" << UHDM::VpiTypeName(obj_h));
        break;
    }
    }

    return nullptr;
}

std::vector<AstNodeModule*> visit_designs(const std::vector<vpiHandle>& designs,
                                          std::ostream& coverage_report_stream, V3ParseSym* symp) {

    UhdmShared shared;
    shared.m_symp = symp;
    // Package for top-level class definitions
    // Created and added only if there are classes in the design
    AstPackage* class_package = nullptr;
    // Package for other top-level definitions
    AstPackage* designPackagep = nullptr;
    for (auto design : designs) {
        visit_one_to_many({UHDM::uhdmallPackages,  // Keep this first, packages need to be defined
                                                   // before any imports
                           // UHDM::uhdmallClasses,
                           UHDM::uhdmallInterfaces, UHDM::uhdmallModules, UHDM::uhdmtopModules},
                          design, shared, [&](AstNode* module) {
                              if (module != nullptr) {
                                  // Top level nodes need to be NodeModules (created from design)
                                  // This is true as we visit only top modules and interfaces (with
                                  // the same AST node) above
                                  shared.top_nodes[module->name()]
                                      = (reinterpret_cast<AstNodeModule*>(module));
                              }
                              for (auto entry : shared.coverage_set) {
                                  coverage_report_stream << std::get<0>(entry) << ":"
                                                         << std::get<1>(entry) << ":"
                                                         << std::get<2>(entry) << std::endl;
                              }
                              shared.coverage_set.clear();
                          });
        // Top level class definitions
        visit_one_to_many(
            {
                UHDM::uhdmallClasses,
            },
            design, shared, [&](AstNode* class_def) {
                if (class_def != nullptr) {
                    if (class_package == nullptr) {
                        class_package = new AstPackage(new FileLine("uhdm"), "AllClasses");
                    }
                    UINFO(6, "Adding class " << class_def->name() << std::endl);
                    class_package->addStmtp(class_def);
                }
                for (auto entry : shared.coverage_set) {
                    coverage_report_stream << std::get<0>(entry) << ":" << std::get<1>(entry)
                                           << ":" << std::get<2>(entry) << std::endl;
                }
                shared.coverage_set.clear();
            });

        vpiHandle typedef_itr = vpi_iterate(vpiTypedef, design);
        while (vpiHandle typedef_obj = vpi_scan(typedef_itr)) {
            AstNode* typedefp = process_typedef(typedef_obj, shared);
            if (typedefp != nullptr) {
                if (designPackagep == nullptr)
                    designPackagep = v3Global.rootp()->dollarUnitPkgAddp();
                designPackagep->addStmtp(typedefp);
            }
        }

        visit_one_to_many(
            {
                vpiTaskFunc,
            },
            design, shared, [&](AstNode* itemp) {
                if (itemp != nullptr) {
                     if (designPackagep == nullptr)
                         designPackagep = v3Global.rootp()->dollarUnitPkgAddp();
                     designPackagep->addStmtp(itemp); }
            });
    }
    if (designPackagep != nullptr)
        shared.m_symp->reinsert(designPackagep, symp->symRootp());

    std::vector<AstNodeModule*> nodes;
    for (auto node : shared.top_nodes) if (!node.second->user1u().toInt()) nodes.push_back(node.second);
    if (class_package != nullptr) { nodes.push_back(class_package); }
    return nodes;
}

}  // namespace UhdmAst
