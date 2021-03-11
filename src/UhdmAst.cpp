#include <vector>
#include <stack>
#include <functional>
#include <algorithm>
#include <regex>

#include "headers/uhdm.h"

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
            vpi_free_object(vpi_child_obj);
        }
        vpi_free_object(itr);
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
        vpi_free_object(itr);
    }
}

void sanitize_str(std::string& s) {
    if (!s.empty()) {
        auto pos = s.find_last_of("@");
        s = s.substr(pos + 1);
        // Replace [ and ], seen in GenScope names
        s = std::regex_replace(s, std::regex("\\["), "__BRA__");
        s = std::regex_replace(s, std::regex("\\]"), "__KET__");
    }
}

bool is_imported(vpiHandle obj_h) {
    if (auto s = vpi_get_str(vpiImported, obj_h)) {
        return true;
    } else {
        return false;
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

AstNode* get_value_as_node(vpiHandle obj_h) {
    AstNode* value_node = nullptr;
    s_vpi_value val;
    vpi_get_value(obj_h, &val);
    switch (val.format) {
    case vpiScalarVal: {
        std::string valStr = std::to_string(val.value.scalar);
        if (valStr[0] == '-') {
            valStr = valStr.substr(1);
            V3Number value(value_node, valStr.c_str());
            auto* inner = new AstConst(new FileLine("uhdm"), value);
            value_node = new AstNegate(new FileLine("uhdm"), inner);
            break;
        }
        V3Number value(value_node, valStr.c_str());
        value_node = new AstConst(new FileLine("uhdm"), value);
        break;
    }
    case vpiIntVal: {
        std::string valStr;
        if (auto s = vpi_get_str(vpiDecompile, obj_h)) {
            valStr = s;
        } else {
            valStr = std::to_string(val.value.integer);
            if (valStr[0] == '-') {
                valStr = valStr.substr(1);
                V3Number value(value_node, valStr.c_str());
                auto* inner = new AstConst(new FileLine("uhdm"), value);
                value_node = new AstNegate(new FileLine("uhdm"), inner);
                break;
            }
        }
        V3Number value(value_node, valStr.c_str());
        value_node = new AstConst(new FileLine("uhdm"), value);
        break;
    }
    case vpiRealVal: {
        std::string valStr = std::to_string(val.value.real);
        V3Number value(value_node, valStr.c_str());
        value_node = new AstConst(new FileLine("uhdm"), value);
        break;
    }
    case vpiBinStrVal:
    case vpiOctStrVal:
    case vpiDecStrVal:
    case vpiHexStrVal: {
        std::string valStr;
        if (auto s = vpi_get_str(vpiDecompile, obj_h)) {
            valStr = s;
        } else {
            // if vpiDecompile is unavailable i.e. in EnumConst, cast the string
            // size is stored in enum typespec
            if (val.format == vpiBinStrVal)
                valStr = "'b" + std::string(val.value.str);
            else if (val.format == vpiOctStrVal)
                valStr = "'o" + std::string(val.value.str);
            else if (val.format == vpiDecStrVal)
                valStr = "'d" + std::string(val.value.str);
            else if (val.format == vpiHexStrVal)
                valStr = "'h" + std::string(val.value.str);
        }
        auto size = vpi_get(vpiSize, obj_h);
        V3Number value(value_node, valStr.c_str());
        value_node = new AstConst(new FileLine("uhdm"), value);
        break;
    }
    case vpiStringVal: {
        std::string valStr(val.value.str);
        value_node = new AstConst(new FileLine("uhdm"), AstConst::VerilogStringLiteral(),
                                  deQuote(new FileLine("uhdm"), valStr));
        break;
    }
    default: {
        break;
    }
    }
    return value_node;
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
    case vpiBitTypespec:
    case vpiBitVar: {
        return AstBasicDTypeKwd::BIT;
    }
    case vpiByteTypespec:
    case vpiByteVar: {
        return AstBasicDTypeKwd::BYTE;
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
    case vpiEnumTypespec:
    case vpiEnumVar:
    case vpiEnumNet:
    case vpiStructTypespec:
    case vpiStructNet:
    case vpiStructVar:
    case vpiUnionTypespec: {
        // Not a basic dtype, needs further handling
        return AstBasicDTypeKwd::UNKNOWN;
    }
    default: v3error("Unknown object type");
    }
    return AstBasicDTypeKwd::UNKNOWN;
}

AstNodeDType* getDType(vpiHandle obj_h, UhdmShared& shared) {
    AstNodeDType* dtype = nullptr;
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
            return new AstIfaceRefDType(new FileLine("uhdm"), cellName, ifaceName);
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
    case vpiIntegerNet:
    case vpiTimeNet:
    case vpiLogicVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiIntegerVar:
    case vpiBitVar:
    case vpiByteVar:
    case vpiRealVar:
    case vpiStringVar:
    case vpiTimeVar:
    case vpiLogicTypespec:
    case vpiIntTypespec:
    case vpiLongIntTypespec:
    case vpiIntegerTypespec:
    case vpiBitTypespec:
    case vpiByteTypespec:
    case vpiRealTypespec:
    case vpiStringTypespec:
    case vpiTimeTypespec: {
        AstBasicDTypeKwd keyword = get_kwd_for_type(type);
        auto basic = new AstBasicDType(new FileLine("uhdm"), keyword);
        AstRange* rangeNode = nullptr;
        std::stack<AstRange*> range_stack;
        visit_one_to_many({vpiRange}, obj_h, shared, [&](AstNode* node) {
            rangeNode = reinterpret_cast<AstRange*>(node);
            range_stack.push(rangeNode);
        });
        rangeNode = nullptr;
        while (!range_stack.empty()) {
            if (rangeNode == nullptr) {
                // Last node serves for basic type
                rangeNode = range_stack.top();
                basic->rangep(rangeNode);
                dtype = basic;
            } else {
                // For other levels create a PackedArray
                rangeNode = range_stack.top();
                dtype = new AstPackArrayDType(new FileLine("uhdm"), VFlagChildDType(), dtype,
                                              rangeNode);
            }
            range_stack.pop();
        }
        if (dtype == nullptr) { dtype = basic; }
        break;
    }
    case vpiEnumNet:
    case vpiStructNet:
    case vpiEnumVar:
    case vpiEnumTypespec:
    case vpiStructTypespec:
    case vpiStructVar:
    case vpiUnionTypespec: {
        std::string type_string;
        const uhdm_handle* const handle = (const uhdm_handle*)obj_h;
        const UHDM::BaseClass* const object = (const UHDM::BaseClass*)handle->object;
        std::string type_name = "";
        if (auto s = vpi_get_str(vpiName, obj_h)) { type_name = s; }
        sanitize_str(type_name);
        if (shared.visited_types.find(object) != shared.visited_types.end()) {
            type_string = shared.visited_types[object];
            size_t delimiter_pos = type_string.find("::");
            if (delimiter_pos == string::npos) {
                UINFO(7, "No package prefix found, creating ref" << std::endl);
                dtype = new AstRefDType(new FileLine("uhdm"), type_string);
            } else {
                auto classpackageName = type_string.substr(0, delimiter_pos);
                auto type_name = type_string.substr(delimiter_pos + 2, type_string.length());
                UINFO(7, "Found package prefix: " << classpackageName << std::endl);
                // If we are in the same package - do not create reference,
                // as it will confuse Verilator
                if (classpackageName
                    == shared.package_prefix.substr(0, shared.package_prefix.length() - 2)) {
                    UINFO(7, "In the same package, creating simple ref" << std::endl);
                    dtype = new AstRefDType(new FileLine("uhdm"), type_name);
                } else {
                    UINFO(7, "Creating ClassOrPackageRef" << std::endl);
                    AstPackage* classpackagep = nullptr;
                    auto it = shared.package_map.find(classpackageName);
                    if (it != shared.package_map.end()) { classpackagep = it->second; }
                    AstNode* classpackageref = new AstClassOrPackageRef(
                        new FileLine("uhdm"), classpackageName, classpackagep, nullptr);
                    shared.m_symp->nextId(classpackagep);
                    dtype = new AstRefDType(new FileLine("uhdm"), type_name, classpackageref,
                                            nullptr);
                }
            }
        } else if (type_name != "") {
            // Type not found or object pointer mismatch, but let's try to create a reference
            // to be resolved later
            // Simple reference only, prefix is not stored in name
            UINFO(7, "No match found, creating ref to name" << type_name << std::endl);
            dtype = new AstRefDType(new FileLine("uhdm"), type_name);
        } else {
            // Typedefed types were visited earlier, probably anonymous struct
            // Get the typespec here
            UINFO(7, "Encountered anonymous struct");
            AstNode* typespec_p = visit_object(obj_h, shared);
            dtype = typespec_p->getChildDTypep()->cloneTree(false);
        }
        break;
    }
    case vpiPackedArrayNet:
    case vpiPackedArrayVar: {
        // Get the typespec
        vpiHandle element_h;
        auto itr = vpi_iterate(vpiElement, obj_h);
        while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
            // Expect all elements to be the same - grab just one
            element_h = vpi_child_obj;
        }
        auto typespec_h = vpi_handle(vpiTypespec, element_h);
        if (typespec_h) {
            dtype = getDType(element_h, shared);
        } else {
            v3error("Missing typespec for unpacked/packed_array_var");
        }
        AstRange* rangep = nullptr;

        visit_one_to_many({vpiRange}, obj_h, shared,
                          [&](AstNode* node) { rangep = reinterpret_cast<AstRange*>(node); });

        dtype = new AstPackArrayDType(new FileLine("uhdm"), VFlagChildDType(), dtype, rangep);
        break;
    }
    case vpiArrayVar: {
        auto array_type = vpi_get(vpiArrayType, obj_h);
        // todo: static/dynamic/assoc/queue
        auto rand_type = vpi_get(vpiRandType, obj_h);
        // todo: rand/randc/notrand
        AstNodeDType* element_dtype = nullptr;

        vpiHandle itr = vpi_iterate(vpiReg, obj_h);
        while (vpiHandle member_h = vpi_scan(itr)) {
            std::string type_name;
            auto type_h = vpi_handle(vpiTypespec, member_h);
            if (type_h) { element_dtype = getDType(type_h, shared); }
            vpi_free_object(member_h);
        }
        vpi_free_object(itr);

        AstRange* range = nullptr;
        visit_one_to_many({vpiRange}, obj_h, shared, [&](AstNode* item) {
            if (item != nullptr) { range = reinterpret_cast<AstRange*>(item); }
        });
        dtype = new AstUnpackArrayDType(new FileLine("uhdm"), VFlagChildDType(), element_dtype,
                                        range);
        break;
    }
    case vpiArrayNet: {
        AstRange* unpacked_range = nullptr;
        AstNodeDType* subDTypep = nullptr;

        vpiHandle itr = vpi_iterate(vpiNet, obj_h);
        while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
            subDTypep = getDType(vpi_child_obj, shared);
            vpi_free_object(vpi_child_obj);
        }
        vpi_free_object(itr);

        visit_one_to_many({vpiRange}, obj_h, shared, [&](AstNode* node) {
            if ((node != nullptr) && (unpacked_range == nullptr)) {
                unpacked_range = reinterpret_cast<AstRange*>(node);
            }
        });

        if ((subDTypep == nullptr) || (unpacked_range == nullptr)) {
            v3error("Missing net and/or unpacked range");
            return nullptr;
        }

        dtype = new AstUnpackArrayDType(new FileLine("uhdm"), VFlagChildDType(), subDTypep,
                                        unpacked_range);
        break;
    }
    default: v3error("Unknown object type: " << UHDM::VpiTypeName(obj_h));
    }
    return dtype;
}

AstNode* process_assignment(vpiHandle obj_h, UhdmShared& shared) {
    AstNode* lvaluep = nullptr;
    AstNode* rvaluep = nullptr;
    const unsigned int objectType = vpi_get(vpiType, obj_h);

    // Right
    visit_one_to_one({vpiRhs}, obj_h, shared, [&](AstNode* childp) { rvaluep = childp; });

    // Left
    visit_one_to_one({vpiLhs}, obj_h, shared, [&](AstNode* childp) { lvaluep = childp; });

    if (rvaluep != nullptr && rvaluep->type() == AstType::en::atFOpen) {
        // Not really an assignpment, AstFOpen node takes care of the lhs
        return rvaluep;
    }
    if (lvaluep && rvaluep) {
        if (objectType == vpiAssignment) {
            auto blocking = vpi_get(vpiBlocking, obj_h);
            if (blocking) {
                return new AstAssign(new FileLine("uhdm"), lvaluep, rvaluep);
            } else {
                return new AstAssignDly(new FileLine("uhdm"), lvaluep, rvaluep);
            }
        } else {
            AstNode* assignp;
            if (lvaluep->type() == AstType::en::atVar) {
                // This is not a true assignpment
                // Set initial value to a variable and return it
                AstVar* varp = static_cast<AstVar*>(lvaluep);
                varp->valuep(rvaluep);
                return varp;
            } else {
                if (objectType == vpiContAssign)
                    assignp = new AstAssignW(new FileLine("uhdm"), lvaluep, rvaluep);
                else
                    assignp = new AstAssign(new FileLine("uhdm"), lvaluep, rvaluep);
                return assignp;
            }
        }
    }
    v3error("Failed to handle assignment");
    return nullptr;
}

AstNode* process_genScopeArray(vpiHandle obj_h, UhdmShared& shared) {
    AstNode* statementsp = nullptr;
    std::string objectName;
    if (auto s = vpi_get_str(vpiName, obj_h)) {
        objectName = s;
        sanitize_str(objectName);
    }
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
        auto* truep = new AstConst(new FileLine("uhdm"), AstConst::Unsized32(), 1);
        auto* blockp = new AstBegin(new FileLine("uhdm"), objectName, statementsp, true, false);
        auto* scopep = new AstGenIf(new FileLine("uhdm"), truep, blockp, nullptr);
        return scopep;
    } else {
        return new AstBegin(new FileLine("uhdm"), "", statementsp);
    }
}

AstNode* process_hierPath(vpiHandle obj_h, UhdmShared& shared) {
        AstNode* lhsp = nullptr;
        AstNode* rhsp = nullptr;

        visit_one_to_many({vpiActual}, obj_h, shared, [&](AstNode* childp) {
            if (lhsp == nullptr) {
                lhsp = childp;
            } else if (rhsp == nullptr) {
                rhsp = childp;
            } else {
                lhsp = new AstDot(new FileLine("uhdm"), false, lhsp, rhsp);
                rhsp = childp;
            }
        });

        return new AstDot(new FileLine("uhdm"), false, lhsp, rhsp);
}

AstNode* visit_object(vpiHandle obj_h, UhdmShared& shared) {
    // Will keep current node
    AstNode* node = nullptr;

    // Current object data
    int lineNo = 0;
    std::string objectName = "";
    std::string fullObjectName = "";

    // For iterating over child objects
    vpiHandle itr;

    auto file_name = vpi_get_str(vpiFile, obj_h);
    if (auto s = vpi_get_str(vpiFullName, obj_h)) {
        fullObjectName = s;
        sanitize_str(fullObjectName);
    }
    for (auto name : {vpiName, vpiFullName, vpiDefName}) {
        if (auto s = vpi_get_str(name, obj_h)) {
            objectName = s;
            sanitize_str(objectName);
            break;
        }
    }
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
        auto* package = new AstPackage(new FileLine(objectName), objectName);
        package->inLibrary(true);
        shared.package_prefix += objectName + "::";
        shared.m_symp->pushNew(package);
        visit_one_to_many(
            {
                vpiTypedef,
                vpiParameter,
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
        for (auto net : {vpiNet, vpiNetArray, vpiArrayVar, vpiArrayNet, vpiVariables}) {
            vpiHandle itr = vpi_iterate(net, parent_h);
            while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
                if (auto s = vpi_get_str(vpiName, vpi_child_obj)) {
                    netName = s;
                    sanitize_str(netName);
                    UINFO(7, "Net name is " << netName << std::endl);
                }
                if (netName == objectName) {
                    UINFO(7, "Found matching net for " << objectName << std::endl);
                    dtype = getDType(vpi_child_obj, shared);
                    break;
                }
                vpi_free_object(vpi_child_obj);
            }
            vpi_free_object(itr);
        }
        if (dtype == nullptr) {
            // If no matching net was found, get info from port node connections
            // This is the case for interface ports
            dtype = getDType(obj_h, shared);
        }
        if (VN_IS(dtype, IfaceRefDType)) {
            var = new AstVar(new FileLine("uhdm"), AstVarType::IFACEREF, objectName,
                             VFlagChildDType(), dtype);
        } else {
            var = new AstVar(new FileLine("uhdm"), AstVarType::PORT, objectName, VFlagChildDType(),
                             dtype);

            if (const int n = vpi_get(vpiDirection, obj_h)) {
                v3info("Got direction for " << objectName);
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
                v3info("Got no direction for " << objectName << ", skipping");
                return nullptr;
            }
        }

        port = new AstPort(new FileLine("uhdm"), ++numPorts, objectName);
        port->addNextNull(var);

        if (v3Global.opt.trace()) { var->trace(true); }

        return port;
    }
    case UHDM::uhdmimport: {
        AstPackage* packagep = nullptr;
        auto it = shared.package_map.find(objectName);
        if (it != shared.package_map.end()) { packagep = it->second; }
        if (packagep != nullptr) {
            std::string symbol_name;
            vpiHandle imported_name = vpi_handle(vpiImport, obj_h);
            if (imported_name) {
                s_vpi_value val;
                vpi_get_value(imported_name, &val);
                symbol_name = val.value.str;
            }
            auto* package_import
                = new AstPackageImport(new FileLine("uhdm"), packagep, symbol_name);
            shared.m_symp->importItem(packagep, symbol_name);
            return package_import;
        }
    }
    case vpiModule: {

        std::string modType = vpi_get_str(vpiDefName, obj_h);
        sanitize_str(modType);

        std::string name = objectName;
        AstModule* module;

        // Check if we have encountered this object before
        auto it = shared.partial_modules.find(modType);
        auto param_it = shared.top_param_map.find(modType);
        if (it != shared.partial_modules.end()) {
            // Was created before, fill missing
            module = reinterpret_cast<AstModule*>(it->second);
            AstModule* full_module = nullptr;
            if (objectName != modType) {
                static int module_counter;
                // Not a top module, create separate node with proper params
                module = module->cloneTree(false);
                // Use more specific name
                name = modType + "_" + objectName + std::to_string(module_counter++);
            }
            module->name(name);
            shared.m_symp->pushNew(module);
            visit_one_to_many(
                {
                    vpiPort,
                    vpiInterface,
                    vpiInterfaceArray,
                    vpiProcess,
                    vpiContAssign,
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
                    vpiVirtualInterfaceVar,
                    vpiReg,
                    vpiRegArray,
                    vpiMemory,
                    vpiInternalScope,
                    vpiImport,
                    vpiAttribute,
                },
                obj_h, shared, [&](AstNode* node) {
                    if (node != nullptr) module->addStmtp(node);
                });
            // Update parameter values using TopModules tree
            if (param_it != shared.top_param_map.end()) {
                auto param_map = param_it->second;
                visit_one_to_many(
                    {
                        vpiParameter,
                        vpiParamAssign,
                    },
                    obj_h, shared, [&](AstNode* node) {
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
            (shared.top_nodes)[name] = module;
            shared.m_symp->popScope(module);
        } else {
            // Encountered for the first time
            module = new AstModule(new FileLine(modType), modType);
            NameNodeMap param_map;
            visit_one_to_many(
                {
                    vpiTypedef,  // Keep this before parameters
                    vpiModule,
                    vpiContAssign,
                    vpiProcess,
                    vpiTaskFunc,
                },
                obj_h, shared, [&](AstNode* node) {
                    if (node != nullptr) module->addStmtp(node);
                });
            visit_one_to_many(
                {
                    vpiParamAssign,
                    vpiParameter,
                },
                obj_h, shared, [&](AstNode* node) {
                    if (node != nullptr) param_map[node->name()] = node;
                });
            (shared.partial_modules)[module->name()] = module;
            shared.top_param_map[module->name()] = param_map;
        }

        if (objectName != modType) {
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
                AstPin* pin = new AstPin(new FileLine("uhdm"), ++np, portName, ref);
                if (!modPins)
                    modPins = pin;
                else
                    modPins->addNextNull(pin);

                vpi_free_object(vpi_child_obj);
            }
            vpi_free_object(itr);

            // Get parameter assignments
            itr = vpi_iterate(vpiParamAssign, obj_h);
            std::set<std::string> parameter_set;
            while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
                vpiHandle param_handle = vpi_handle(vpiLhs, vpi_child_obj);
                std::string param_name = vpi_get_str(vpiName, param_handle);
                sanitize_str(param_name);
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
                    AstPin* pin = new AstPin(new FileLine("uhdm"), ++np, param_name, value);
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
                vpi_free_object(vpi_child_obj);
            }
            vpi_free_object(itr);
            std::string fullname = vpi_get_str(vpiFullName, obj_h);
            sanitize_str(fullname);
            UINFO(8, "Adding cell " << fullname << std::endl);
            AstCell* cell = new AstCell(new FileLine("uhdm"), new FileLine("uhdm"), objectName,
                                        name, modPins, modParams, nullptr);
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
    case vpiRefObj: {
        size_t dot_pos = objectName.rfind('.');
        if (dot_pos != std::string::npos) {
            // TODO: Handle >1 dot
            std::string lhs = objectName.substr(0, dot_pos);
            std::string rhs = objectName.substr(dot_pos + 1, objectName.length());
            AstParseRef* lhsNode = new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT,
                                                   lhs, nullptr, nullptr);
            AstParseRef* rhsNode = new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT,
                                                   rhs, nullptr, nullptr);

            return new AstDot(new FileLine("uhdm"), false, lhsNode, rhsNode);
        } else {
            bool isLvalue = false;
            vpiHandle actual = vpi_handle(vpiActual, obj_h);
            if (actual) {
                auto actual_type = vpi_get(vpiType, actual);
                if (actual_type == vpiPort) {
                    if (const int n = vpi_get(vpiDirection, actual)) {
                        if (n == vpiInput) {
                            isLvalue = false;
                        } else if (n == vpiOutput) {
                            isLvalue = true;
                        } else if (n == vpiInout) {
                            isLvalue = true;
                        }
                    }
                }
                vpi_free_object(actual);
            }
            return new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT, objectName,
                                   nullptr, nullptr);
        }
        break;
    }
    case vpiNetArray: {  // also defined as vpiArrayNet
        // vpiNetArray is used for unpacked arrays
        AstVar* vpi_net = nullptr;
        visit_one_to_many({vpiNet}, obj_h, shared, [&](AstNode* node) {
            if ((node != nullptr) && (vpi_net == nullptr)) {
                vpi_net = reinterpret_cast<AstVar*>(node);
            }
        });

        auto dtypep = getDType(obj_h, shared);
        AstVar* v = new AstVar(new FileLine("uhdm"), vpi_net->varType(), objectName,
                               VFlagChildDType(), dtypep);
        return v;
    }

    case vpiEnumNet:
    case vpiStructNet:
    case vpiIntegerNet:
    case vpiTimeNet:
    case vpiPackedArrayNet:
    case vpiLogicNet: {  // also defined as vpiNet
        AstNodeDType* dtype = nullptr;
        AstVarType net_type = AstVarType::VAR;
        AstBasicDTypeKwd dtypeKwd = AstBasicDTypeKwd::LOGIC_IMPLICIT;
        vpiHandle obj_net;
        dtype = getDType(obj_h, shared);

        if (net_type == AstVarType::UNKNOWN && dtype == nullptr) {
            // Not set in case above, most likely a "false" port net
            return nullptr;  // Skip this net
        }

        return new AstVar(new FileLine("uhdm"), net_type, objectName, VFlagChildDType(), dtype);
    }
    case vpiStructVar: {
        AstNodeDType* dtype = getDType(obj_h, shared);

        auto* v = new AstVar(new FileLine("uhdm"), AstVarType::VAR, objectName, VFlagChildDType(),
                             dtype);
        return v;
    }
    case vpiParameter:
    case vpiParamAssign: {
        AstVar* parameter = nullptr;
        AstNode* parameter_value = nullptr;
        vpiHandle parameter_h;

        if (objectType == vpiParamAssign) {
            parameter_h = vpi_handle(vpiLhs, obj_h);
            // Update object name using parameter handle
            if (auto s = vpi_get_str(vpiName, parameter_h)) {
                objectName = s;
                sanitize_str(objectName);
            }
        } else if (objectType == vpiParameter) {
            parameter_h = obj_h;
        }
        if (is_imported(parameter_h)) {
            // Skip imported parameters, they will still be visible in their packages
            UINFO(3, "Skipping imported parameter " << objectName << std::endl);
            return nullptr;
        }

        AstRange* rangeNode = nullptr;
        visit_one_to_many({vpiRange}, parameter_h, shared, [&](AstNode* node) {
            if (node) rangeNode = reinterpret_cast<AstRange*>(node);
        });

        AstNodeDType* dtype = nullptr;
        auto typespec_h = vpi_handle(vpiTypespec, parameter_h);
        if (typespec_h) { dtype = getDType(typespec_h, shared); }

        // If no typespec provided assume default
        if (dtype == nullptr) {
            auto* temp_dtype
                = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::LOGIC_IMPLICIT);
            dtype = temp_dtype;
        }
        if (rangeNode) {
            dtype = new AstUnpackArrayDType(new FileLine("uhdm"), VFlagChildDType(), dtype,
                                            rangeNode);
        }
        AstVarType parameter_type;
        int is_local = 0;

        // Get value
        if (objectType == vpiParamAssign) {
            visit_one_to_one({vpiRhs}, obj_h, shared,
                             [&](AstNode* node) { parameter_value = node; });
            is_local = vpi_get(vpiLocalParam, vpi_handle(vpiLhs, obj_h));
        } else if (objectType == vpiParameter) {
            parameter_value = get_value_as_node(obj_h);
            is_local = vpi_get(vpiLocalParam, obj_h);
        }

        if (is_local)
            parameter_type = AstVarType::LPARAM;
        else
            parameter_type = AstVarType::GPARAM;

        // if no value: bail
        if (parameter_value == nullptr) {
            return nullptr;
        } else {
            parameter = new AstVar(new FileLine("uhdm"), parameter_type, objectName,
                                   VFlagChildDType(), dtype);
            parameter->valuep(parameter_value);
            return parameter;
        }
    }
    case vpiInterface: {
        // Interface definition is represented by a module node
        AstIface* elaboratedInterface = new AstIface(new FileLine("uhdm"), objectName);
        bool hasModports = false;
        visit_one_to_many(
            {
                vpiPort,
                vpiParameter,
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
            },
            obj_h, shared, [&](AstNode* port) {
                if (port) { elaboratedInterface->addStmtp(port); }
            });
        visit_one_to_many({vpiModport}, obj_h, shared, [&](AstNode* port) {
            if (port) {
                hasModports = true;
                elaboratedInterface->addStmtp(port);
            }
        });
        if (hasModports) {
            // Only then create the nets, as they won't be connected otherwise
            visit_one_to_many({vpiNet}, obj_h, shared, [&](AstNode* port) {
                if (port) { elaboratedInterface->addStmtp(port); }
            });
        }

        elaboratedInterface->name(objectName);
        std::string modType = vpi_get_str(vpiDefName, obj_h);
        sanitize_str(modType);
        if (objectName != modType) {
            AstPin* modPins = nullptr;
            vpiHandle itr = vpi_iterate(vpiPort, obj_h);
            int np = 0;
            while (vpiHandle vpi_child_obj = vpi_scan(itr)) {
                vpiHandle highConn = vpi_handle(vpiHighConn, vpi_child_obj);
                if (highConn) {
                    std::string portName = vpi_get_str(vpiName, vpi_child_obj);
                    sanitize_str(portName);
                    AstParseRef* ref
                        = reinterpret_cast<AstParseRef*>(visit_object(highConn, shared));
                    AstPin* pin = new AstPin(new FileLine("uhdm"), ++np, portName, ref);
                    if (!modPins)
                        modPins = pin;
                    else
                        modPins->addNextNull(pin);
                }

                vpi_free_object(vpi_child_obj);
            }
            vpi_free_object(itr);

            AstCell* cell = new AstCell(new FileLine("uhdm"), new FileLine("uhdm"), objectName,
                                        modType, modPins, nullptr, nullptr);
            return cell;
        } else {
            // is top level
            return elaboratedInterface;
        }
        break;
    }
    case vpiModport: {
        AstNode* modport_vars = nullptr;

        // We construct a reference here, the net is created in the interface
        // No full visit, just grab name and direction
        auto io_itr = vpi_iterate(vpiIODecl, obj_h);
        while (vpiHandle io_h = vpi_scan(io_itr)) {
            std::string io_name;
            if (auto s = vpi_get_str(vpiName, io_h)) {
                io_name = s;
                sanitize_str(io_name);
            }
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
            auto* io_node = new AstModportVarRef(new FileLine("uhdm"), io_name, dir);
            if (modport_vars)
                modport_vars->addNextNull(io_node);
            else
                modport_vars = io_node;
            vpi_free_object(io_h);
        }
        vpi_free_object(io_itr);

        return new AstModport(new FileLine("uhdm"), objectName, modport_vars);
    }
    case vpiIODecl: {
        // For function arguments, the actual type
        // is inside vpiExpr
        AstNode* expr = nullptr;
        visit_one_to_one({vpiExpr}, obj_h, shared, [&](AstNode* item) {
            if (item) { expr = item; }
        });
        if (expr != nullptr) {
            // Override name with IO name
            expr->name(objectName);
            return expr;
        }  // else handle as normal IODecl

        VDirection dir;
        if (const int n = vpi_get(vpiDirection, obj_h)) {
            if (n == vpiInput) {
                dir = VDirection::INPUT;
            } else if (n == vpiOutput) {
                dir = VDirection::OUTPUT;
            } else if (n == vpiInout) {
                dir = VDirection::INOUT;
            }
        }

        AstRange* var_range = nullptr;
        visit_one_to_many({vpiRange}, obj_h, shared, [&](AstNode* item) {
            if (item) { var_range = reinterpret_cast<AstRange*>(item); }
        });
        auto* dtype = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::LOGIC);
        dtype->rangep(var_range);
        auto* var = new AstVar(new FileLine("uhdm"), AstVarType::PORT, objectName,
                               VFlagChildDType(), dtype);
        var->declDirection(dir);
        var->direction(dir);
        return var;
    }
    case vpiAlways: {
        VAlwaysKwd alwaysType;
        AstSenTree* senTree = nullptr;
        AstNode* body = nullptr;

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

        if (alwaysType != VAlwaysKwd::ALWAYS_COMB && alwaysType != VAlwaysKwd::ALWAYS_LATCH) {
            // Handled in vpiEventControl
            AstNode* always;

            visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* node) { always = node; });
            return always;
        } else {
            // Body of statements
            visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* node) { body = node; });
        }

        return new AstAlways(new FileLine("uhdm"), alwaysType, senTree, body);
    }
    case vpiEventControl: {
        AstSenItem* senItemRoot;
        AstNode* body = nullptr;
        AstSenTree* senTree = nullptr;
        visit_one_to_one({vpiCondition}, obj_h, shared, [&](AstNode* node) {
            if (node->type() == AstType::en::atSenItem) {
                senItemRoot = reinterpret_cast<AstSenItem*>(node);
            } else {  // wrap this in a AstSenItem
                senItemRoot = new AstSenItem(new FileLine("uhdm"), VEdgeType::ET_ANYEDGE, node);
            }
        });
        senTree = new AstSenTree(new FileLine("uhdm"), senItemRoot);
        // Body of statements
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* node) { body = node; });
        auto* tctrl = new AstTimingControl(new FileLine("uhdm"), senTree, body);
        return new AstAlways(new FileLine("uhdm"), VAlwaysKwd::ALWAYS_FF, nullptr, tctrl);
    }
    case vpiInitial: {
        AstNode* body = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* node) { body = node; });
        return new AstInitial(new FileLine("uhdm"), body);
    }
    case vpiFinal: {
        AstNode* body = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* node) { body = node; });
        return new AstFinal(new FileLine("uhdm"), body);
    }
    case vpiNamedBegin:
    case vpiBegin: {
        AstNode* body = nullptr;
        visit_one_to_many(
            {
                vpiTypedef,
                vpiStmt,
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
                vpiParameter,
                vpiParamAssign,
                vpiInternalScope,
                vpiImport,
                vpiAttribute,
                vpiNet,
            },
            obj_h, shared, [&](AstNode* node) {
                if (body == nullptr) {
                    body = node;
                } else {
                    body->addNextNull(node);
                }
            });
        if (objectType == vpiBegin) {
            objectName = "";  // avoid storing parent name
        }
        return new AstBegin(new FileLine("uhdm"), "", body);
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
        return new AstIf(new FileLine("uhdm"), condition, statement, elseStatement);
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
        return new AstCase(new FileLine("uhdm"), case_type, conditionNode, itemNodes);
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
        return new AstCaseItem(new FileLine("uhdm"), expressionNode, bodyNode);
    }
    case vpiOperation: {
        AstNode* rhs = nullptr;
        AstNode* lhs = nullptr;
        auto operation = vpi_get(vpiOpType, obj_h);
        switch (operation) {
        case vpiBitNegOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) { rhs = node; });
            return new AstNot(new FileLine("uhdm"), rhs);
        }
        case vpiNotOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) { lhs = node; });
            return new AstLogNot(new FileLine("uhdm"), lhs);
        }
        case vpiBitAndOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstAnd(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiListOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) {
                    rhs = node;
                } else {
                    rhs->addNextNull(node);
                }
            });
            return rhs;
        }
        case vpiBitOrOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstOr(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiBitXorOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) {
                    rhs = node;
                } else {
                    lhs = node;
                }
            });
            return new AstXor(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiBitXnorOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) {
                    rhs = node;
                } else {
                    lhs = node;
                }
            });
            return new AstXnor(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiPostIncOp:
        case vpiPostDecOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) { rhs = node; }
            });
            auto* one = new AstConst(new FileLine("uhdm"), 1);
            AstNode* op = nullptr;
            if (operation == vpiPostIncOp) {
                op = new AstAdd(new FileLine("uhdm"), rhs, one);
            } else if (operation == vpiPostDecOp) {
                op = new AstSub(new FileLine("uhdm"), rhs, one);
            }
            auto* var = new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT,
                                        rhs->name(), nullptr, nullptr);
            return new AstAssign(new FileLine("uhdm"), var, op);
        }
        case vpiAssignmentOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstAssign(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiUnaryAndOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) { rhs = node; }
            });
            return new AstRedAnd(new FileLine("uhdm"), rhs);
        }
        case vpiUnaryNandOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) { rhs = node; }
            });
            auto* op = new AstRedAnd(new FileLine("uhdm"), rhs);
            return new AstNot(new FileLine("uhdm"), op);
        }
        case vpiUnaryNorOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) { rhs = node; }
            });
            auto* op = new AstRedOr(new FileLine("uhdm"), rhs);
            return new AstNot(new FileLine("uhdm"), op);
        }
        case vpiUnaryOrOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) { rhs = node; }
            });
            return new AstRedOr(new FileLine("uhdm"), rhs);
        }
        case vpiUnaryXorOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) { rhs = node; }
            });
            return new AstRedXor(new FileLine("uhdm"), rhs);
        }
        case vpiUnaryXNorOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (rhs == nullptr) { rhs = node; }
            });
            return new AstRedXnor(new FileLine("uhdm"), rhs);
        }
        case vpiEventOrOp: {
            // Do not create a separate node
            // Chain operand nodes instead
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (node) {
                    if (node->type() == AstType::en::atSenItem) {
                        // This is a Posedge/Negedge operation, keep this node
                        if (rhs == nullptr) {
                            rhs = node;
                        } else {
                            rhs->addNextNull(node);
                        }
                    } else {
                        // Edge not specified -> use ANY
                        auto* wrapper
                            = new AstSenItem(new FileLine("uhdm"), VEdgeType::ET_ANYEDGE, node);
                        if (rhs == nullptr) {
                            rhs = wrapper;
                        } else {
                            rhs->addNextNull(wrapper);
                        }
                    }
                }
            });
            return rhs;
        }
        case vpiLogAndOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstLogAnd(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiLogOrOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstLogOr(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiPosedgeOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) { rhs = node; });
            return new AstSenItem(new FileLine("uhdm"), VEdgeType::ET_POSEDGE, rhs);
        }
        case vpiNegedgeOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) { rhs = node; });
            return new AstSenItem(new FileLine("uhdm"), VEdgeType::ET_NEGEDGE, rhs);
        }
        case vpiEqOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstEq(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiCaseEqOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstEqCase(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiNeqOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstNeq(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiCaseNeqOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstNeqCase(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiGtOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstGt(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiGeOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstGte(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiLtOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstLt(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiLeOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstLte(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiPlusOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstAdd(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiSubOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstSub(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiMinusOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) { lhs = node; }
            });
            return new AstNegate(new FileLine("uhdm"), lhs);
        }
        case vpiAddOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstAdd(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiMultOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstMul(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiDivOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstDiv(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiModOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstModDiv(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiConditionOp: {
            AstNode* condition = nullptr;
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (condition == nullptr) {
                    condition = node;
                } else if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstCond(new FileLine("uhdm"), condition, lhs, rhs);
        }
        case vpiConcatOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (node != nullptr) {
                    if (lhs == nullptr) {
                        lhs = node;
                    } else if (rhs == nullptr) {
                        rhs = node;
                    } else {
                        // Add one more level
                        lhs = new AstConcat(new FileLine("uhdm"), lhs, rhs);
                        rhs = node;
                    }
                }
            });
            // Wrap in a Replicate node
            if (rhs != nullptr) {
                lhs = new AstConcat(new FileLine("uhdm"), lhs, rhs);
                rhs = new AstConst(new FileLine("uhdm"), 1);
            } else {
                rhs = new AstConst(new FileLine("uhdm"), 1);
            }
            return new AstReplicate(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiMultiConcatOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else if (rhs == nullptr) {
                    rhs = node;
                }
            });
            // Sides in AST are switched: first rhs (value), then lhs (count)
            return new AstReplicate(new FileLine("uhdm"), rhs, lhs);
        }
        case vpiArithLShiftOp:  // This behaves the same as normal shift
        case vpiLShiftOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstShiftL(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiRShiftOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstShiftR(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiArithRShiftOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstShiftRS(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiInsideOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (node != nullptr) {
                    if (lhs == nullptr) {
                        lhs = node;
                    } else if (rhs == nullptr) {
                        rhs = node;
                    } else {
                        rhs->addNextNull(node);
                    }
                }
            });
            return new AstInside(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiCastOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) { lhs = node; }
            });
            auto typespec_h = vpi_handle(vpiTypespec, obj_h);
            std::set<int> typespec_types = {
                vpiClassTypespec, vpiEnumTypespec, vpiStructTypespec,
                vpiUnionTypespec, vpiVoidTypespec,
            };
            if (typespec_types.count(vpi_get(vpiType, typespec_h)) != 0) {
                // Custom type, create reference only
                std::string name;
                if (auto s = vpi_get_str(vpiName, typespec_h)) {
                    name = s;
                    sanitize_str(name);
                } else {
                    v3error("Encountered custom, but unnamed typespec");
                }
                return new AstCast(new FileLine("uhdm"), lhs,
                                   new AstRefDType(new FileLine("uhdm"), name));
            } else {
                visit_one_to_one({vpiTypespec}, obj_h, shared, [&](AstNode* node) {
                    if (rhs == nullptr) { rhs = node; }
                });
            }
            return new AstCastParse(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiStreamRLOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else if (rhs == nullptr) {
                    rhs = node;
                }
            });

            // Verilog {rhs{lhs}} - Note rhs() is the slice size, not the lhs()
            // IEEE 11.4.14.2: If a slice_size is not specified, the default is 1.
            if (rhs == nullptr) {
                return new AstStreamL(new FileLine("uhdm"), lhs,
                                      new AstConst(new FileLine("uhdm"), 1));
            } else {
                return new AstStreamL(new FileLine("uhdm"), lhs, rhs);
            }
        }
        case vpiStreamLROp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else if (rhs == nullptr) {
                    rhs = node;
                }
            });
            // See comments above - default rhs is 1
            if (rhs == nullptr) {
                return new AstStreamR(new FileLine("uhdm"), lhs,
                                      new AstConst(new FileLine("uhdm"), 1));
            } else {
                return new AstStreamR(new FileLine("uhdm"), lhs, rhs);
            }
        }
        case vpiPowerOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    rhs = node;
                }
            });
            return new AstPow(new FileLine("uhdm"), lhs, rhs);
        }
        case vpiAssignmentPatternOp: {
            visit_one_to_many({vpiOperand}, obj_h, shared, [&](AstNode* node) {
                // Wrap only if this is a positional pattern
                // Tagged patterns will return member nodes
                if (node && !VN_IS(node, PatMember)) {
                    node = new AstPatMember(new FileLine("uhdm"), node, nullptr, nullptr);
                }
                if (lhs == nullptr) {
                    lhs = node;
                } else {
                    lhs->addNextNull(node);
                }
            });
            return new AstPattern(new FileLine("uhdm"), lhs);
        }
        default: {
            v3error("\t! Encountered unhandled operation: " << operation);
            break;
        }
        }
        return nullptr;
    }
    case vpiTaggedPattern: {
        AstNode* typespec = nullptr;
        AstNode* pattern = nullptr;
        auto typespec_h = vpi_handle(vpiTypespec, obj_h);
        std::string pattern_name;
        if (auto s = vpi_get_str(vpiName, typespec_h)) { pattern_name = s; }
        sanitize_str(pattern_name);
        typespec = new AstText(new FileLine("uhdm"), pattern_name);

        visit_one_to_one({vpiPattern}, obj_h, shared, [&](AstNode* node) { pattern = node; });
        if (pattern_name == "default") {
            auto* patm = new AstPatMember(new FileLine("uhdm"), pattern, nullptr, nullptr);
            patm->isDefault(true);
            return patm;
        } else {
            return new AstPatMember(new FileLine("uhdm"), pattern, typespec, nullptr);
        }
    }
    case vpiEnumConst:
    case vpiConstant: {
        return get_value_as_node(obj_h);
    }
    case vpiBitSelect: {
        auto* fromp = new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT, objectName,
                                      nullptr, nullptr);
        AstNode* bitp = nullptr;
        visit_one_to_one({vpiIndex}, obj_h, shared, [&](AstNode* item) {
            if (item) { bitp = item; }
        });
        return new AstSelBit(new FileLine("uhdm"), fromp, bitp);
    }
    case vpiVarSelect: {
        AstNode* fromp = new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT,
                                         objectName, nullptr, nullptr);
        AstNode* bitp = nullptr;
        AstNode* select = nullptr;
        visit_one_to_many({vpiIndex}, obj_h, shared, [&](AstNode* item) {
            bitp = item;
            if (item->type() == AstType::en::atSelExtract) {
                select = new AstSelExtract(new FileLine("uhdm"), fromp,
                                           ((AstSelExtract*)item)->msbp()->cloneTree(true),
                                           ((AstSelExtract*)item)->lsbp()->cloneTree(true));
            } else if (item->type() == AstType::en::atConst) {
                select = new AstSelBit(new FileLine("uhdm"), fromp, bitp);
            } else if (item->type() == AstType::atSelPlus) {
                AstSelPlus* selplusp = VN_CAST(item, SelPlus);
                select = new AstSelPlus(new FileLine("uhdm"), fromp, selplusp->bitp(),
                                        selplusp->widthp());
            } else if (item->type() == AstType::atSelMinus) {
                AstSelMinus* selminusp = VN_CAST(item, SelMinus);
                select = new AstSelMinus(new FileLine("uhdm"), fromp, selminusp->bitp(),
                                         selminusp->widthp());

            } else {
                select = new AstSelBit(new FileLine("uhdm"), fromp, bitp);
            }
            fromp = select;
        });
        return select;
    }
    case vpiTask: {
        AstNode* statements = nullptr;
        visit_one_to_many({vpiIODecl}, obj_h, shared, [&](AstNode* item) {
            if (item) {
                // Overwrite direction for arguments
                auto* io = reinterpret_cast<AstVar*>(item);
                io->direction(VDirection::INPUT);
                if (statements)
                    statements->addNextNull(item);
                else
                    statements = item;
            }
        });
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* item) {
            if (item) {
                if (statements)
                    statements->addNextNull(item);
                else
                    statements = item;
            }
        });
        return new AstTask(new FileLine("uhdm"), objectName, statements);
    }
    case vpiTaskCall: {
        return new AstTaskRef(new FileLine("uhdm"), objectName, nullptr);
    }
    case vpiFunction: {
        AstNode* statements = nullptr;
        AstNode* function_vars = nullptr;

        AstRange* returnRange = nullptr;
        auto return_h = vpi_handle(vpiReturn, obj_h);
        if (return_h) {
            AstNode* dtype = getDType(return_h, shared);
            function_vars = dtype;
        }

        visit_one_to_many({vpiIODecl}, obj_h, shared, [&](AstNode* item) {
            if (item) {
                // Overwrite direction for arguments
                auto* io = reinterpret_cast<AstVar*>(item);
                io->direction(VDirection::INPUT);
                if (statements)
                    statements->addNextNull(item);
                else
                    statements = item;
            }
        });
        visit_one_to_many({vpiVariables}, obj_h, shared, [&](AstNode* item) {
            if (item) {
                if (statements)
                    statements->addNextNull(item);
                else
                    statements = item;
            }
        });
        visit_one_to_one({vpiStmt}, obj_h, shared, [&](AstNode* item) {
            if (item) {
                if (statements)
                    statements->addNextNull(item);
                else
                    statements = item;
            }
        });
        if (return_h) {
            node = new AstFunc(new FileLine("uhdm"), objectName, statements, function_vars);
        } else {
            node = new AstTask(new FileLine("uhdm"), objectName, statements);
        }
        AstDpiExport* exportp = nullptr;
        auto accessType = vpi_get(vpiAccessType, obj_h);
        if (accessType == vpiDPIExportAcc) {
            exportp = new AstDpiExport(new FileLine("uhdm"), objectName, objectName);
            exportp->addNext(node);
            v3Global.dpi(true);
            return exportp;
        } else {
            return node;
        }
    }
    case vpiReturn:
    case vpiReturnStmt: {
        AstNode* condition = nullptr;
        visit_one_to_one({vpiCondition}, obj_h, shared, [&](AstNode* item) {
            if (item) { condition = item; }
        });
        return new AstReturn(new FileLine("uhdm"), condition);
    }
    case vpiFuncCall: {
        AstNode* arguments = nullptr;
        visit_one_to_many({vpiArgument}, obj_h, shared, [&](AstNode* item) {
            if (item) {
                if (arguments == nullptr) {
                    arguments = new AstArg(new FileLine("uhdm"), "", item);
                } else {
                    arguments->addNextNull(new AstArg(new FileLine("uhdm"), "", item));
                }
            }
        });

        size_t dot_pos = objectName.rfind('.');
        if (dot_pos != std::string::npos) {
            // Split object name into prefix.method
            // TODO: Handle >1 dot, currently all goes into prefix
            std::string lhs = objectName.substr(0, dot_pos);
            std::string rhs = objectName.substr(dot_pos + 1, objectName.length());
            AstParseRef* from = new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT,
                                                lhs, nullptr, nullptr);
            return new AstMethodCall(new FileLine("uhdm"), from, rhs, arguments);
        }
        // Check if this is a task or function by looking for return value
        auto function_h = vpi_handle(vpiFunction, obj_h);
        auto return_h = vpi_handle(vpiReturn, function_h);
        if (return_h)
            return new AstFuncRef(new FileLine("uhdm"), objectName, arguments);
        else
            return new AstTaskRef(new FileLine("uhdm"), objectName, arguments);
    }
    case vpiSysFuncCall: {
        std::vector<AstNode*> arguments;
        visit_one_to_many({vpiArgument}, obj_h, shared, [&](AstNode* item) {
            if (item) { arguments.push_back(item); }
        });

        if (objectName == "$signed") {
            return new AstSigned(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$unsigned") {
            return new AstUnsigned(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$cast") {
            return new AstCastParse(new FileLine("uhdm"), arguments[0], arguments[1]);
        } else if (objectName == "$isunknown") {
            return new AstIsUnknown(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$time") {
            return new AstTime(new FileLine("uhdm"),
                               VTimescale::TS_1PS);  // TODO: revisit once we have it in UHDM
        } else if (objectName == "$display") {
            AstNode* args = nullptr;
            for (auto a : arguments) {
                if (args == nullptr)
                    args = a;
                else
                    args->addNextNull(a);
            }
            return new AstDisplay(new FileLine("uhdm"), AstDisplayType(), nullptr, args);
        } else if (objectName == "$value$plusargs") {
            node = new AstValuePlusArgs(new FileLine("uhdm"), arguments[0], arguments[1]);
        } else if (objectName == "$sformat" || objectName == "$swrite") {
            AstNode* args = nullptr;
            // Start from second argument
            for (auto it = ++arguments.begin(); it != arguments.end(); it++) {
                if (args == nullptr)
                    args = *it;
                else
                    args->addNextNull(*it);
            }
            return new AstSFormat(new FileLine("uhdm"), arguments[0], args);
        } else if (objectName == "$sformatf") {
            AstNode* args = nullptr;
            // Start from second argument
            for (auto it = arguments.begin(); it != arguments.end(); it++) {
                if (args == nullptr)
                    args = *it;
                else
                    args->addNextNull(*it);
            }
            return new AstSFormatF(new FileLine("uhdm"), "", false, args);
        } else if (objectName == "$finish") {
            return new AstFinish(new FileLine("uhdm"));
        } else if (objectName == "$fopen") {
            // We need to obtain the variable in which the descriptor will be stored
            // This usually will be LHS of an assignment fd = $fopen(...)
            auto parent_h = vpi_handle({vpiParent}, obj_h);
            auto lhs_h = vpi_handle({vpiLhs}, parent_h);
            AstNode* fd = nullptr;
            if (lhs_h) { fd = visit_object(lhs_h, shared); }
            return new AstFOpen(new FileLine("uhdm"), fd, arguments[0], arguments[1]);
        } else if (objectName == "$fclose") {
            return new AstFClose(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$fwrite") {
            AstNode* filep = arguments[0];
            arguments.erase(arguments.begin());
            AstNode* args = nullptr;
            for (auto a : arguments) {
                if (args == nullptr)
                    args = a;
                else
                    args->addNextNull(a);
            }
            return new AstDisplay(new FileLine("uhdm"),
                                  AstDisplayType(AstDisplayType::en::DT_WRITE), filep, args);
        } else if (objectName == "$fflush") {
            return new AstFFlush(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$clog2") {
            return new AstCLog2(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$left") {
            if (arguments.size() == 1)
                arguments.push_back(nullptr);  // provide default for optional parameter
            return new AstAttrOf(new FileLine("uhdm"), AstAttrType::DIM_LEFT, arguments[0],
                                 arguments[1]);
        } else if (objectName == "$right") {
            if (arguments.size() == 1)
                arguments.push_back(nullptr);  // provide default for optional parameter
            return new AstAttrOf(new FileLine("uhdm"), AstAttrType::DIM_RIGHT, arguments[0],
                                 arguments[1]);
        } else if (objectName == "$low") {
            if (arguments.size() == 1)
                arguments.push_back(nullptr);  // provide default for optional parameter
            return new AstAttrOf(new FileLine("uhdm"), AstAttrType::DIM_LOW, arguments[0],
                                 arguments[1]);
        } else if (objectName == "$high") {
            if (arguments.size() == 1)
                arguments.push_back(nullptr);  // provide default for optional parameter
            return new AstAttrOf(new FileLine("uhdm"), AstAttrType::DIM_HIGH, arguments[0],
                                 arguments[1]);
        } else if (objectName == "$increment") {
            if (arguments.size() == 1)
                arguments.push_back(nullptr);  // provide default for optional parameter
            return new AstAttrOf(new FileLine("uhdm"), AstAttrType::DIM_RIGHT, arguments[0],
                                 arguments[1]);
        } else if (objectName == "$size") {
            if (arguments.size() == 1)
                arguments.push_back(nullptr);  // provide default for optional parameter
            return new AstAttrOf(new FileLine("uhdm"), AstAttrType::DIM_RIGHT, arguments[0],
                                 arguments[1]);
        } else if (objectName == "$dimensions") {
            return new AstAttrOf(new FileLine("uhdm"), AstAttrType::DIM_DIMENSIONS, arguments[0]);
        } else if (objectName == "$unpacked_dimensions") {
            return new AstAttrOf(new FileLine("uhdm"), AstAttrType::DIM_UNPK_DIMENSIONS,
                                 arguments[0]);
        } else if (objectName == "$bits") {
            // If this is not an expression, explicitly mark it as data type ref.
            // See exprOrDataType in verilog.y
            AstNode* expr_datatype_p = arguments[0];
            if (VN_IS(expr_datatype_p, ParseRef)) {
                expr_datatype_p = new AstRefDType(new FileLine("uhdm"), expr_datatype_p->name());
            }
            return new AstAttrOf(new FileLine("uhdm"), AstAttrType::DIM_BITS, expr_datatype_p);
        } else if (objectName == "$realtobits") {
            return new AstRealToBits(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$bitstoreal") {
            return new AstBitsToRealD(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$readmemh") {
            if (arguments.size() == 2) {
                return new AstReadMem(new FileLine("uhdm"),
                                      true,  // isHex
                                      arguments[0], arguments[1], nullptr, nullptr);
            } else if (arguments.size() == 4) {
                return new AstReadMem(new FileLine("uhdm"),
                                      true,  // isHex
                                      arguments[0], arguments[1], arguments[2], arguments[3]);
            }
        } else if (objectName == "$readmemb") {
            if (arguments.size() == 2) {
                return new AstReadMem(new FileLine("uhdm"),
                                      false,  // isHex
                                      arguments[0], arguments[1], nullptr, nullptr);
            } else if (arguments.size() == 4) {
                return new AstReadMem(new FileLine("uhdm"),
                                      false,  // isHex
                                      arguments[0], arguments[1], arguments[2], arguments[3]);
            }
        } else if (objectName == "$info" || objectName == "$warning" || objectName == "$error"
                   || objectName == "$fatal") {

            AstDisplayType type;
            if (objectName == "$info") {
                type = AstDisplayType::DT_INFO;
            } else if (objectName == "$warning") {
                type = AstDisplayType::DT_WARNING;
            } else if (objectName == "$error") {
                type = AstDisplayType::DT_ERROR;
            } else if (objectName == "$fatal") {
                type = AstDisplayType::DT_FATAL;
                // Verilator discards the finish number - first argument
                if (arguments.size()) arguments.erase(arguments.begin());
            }

            AstNode* args = nullptr;
            for (auto a : arguments) {
                if (args == nullptr)
                    args = a;
                else
                    args->addNextNull(a);
            }
            node = new AstDisplay(new FileLine("uhdm"), type, nullptr, args);
            if (type == AstDisplayType::DT_ERROR || type == AstDisplayType::DT_FATAL) {
                auto* stop = new AstStop(new FileLine("uhdm"), (type == AstDisplayType::DT_ERROR));
                node->addNext(stop);
            }
            return node;
        } else if (objectName == "$__BAD_SYMBOL__") {
            v3info("\t! Bad symbol encountered @ " << file_name << ":" << currentLine);
            // Dummy statement to keep parsing
            return new AstTime(new FileLine("uhdm"),
                               VTimescale::TS_1PS);  // TODO: revisit once we have it in UHDM
        } else {
            v3error("\t! Encountered unhandled SysFuncCall: " << objectName);
        }
        auto parent_h = vpi_handle(vpiParent, obj_h);
        int parent_type = 0;
        if (parent_h) { parent_type = vpi_get(vpiType, parent_h); }
        if (parent_type == vpiBegin) {  // TODO: Are other contexts missing here?
            // In task-like context return values are discarded
            // This is indicated by wrapping the node
            return new AstSysFuncAsTask(new FileLine("uhdm"), node);
        } else {
            return node;
        }
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
            rangeNode = new AstRange(new FileLine("uhdm"), msbNode, lsbNode);
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
            std::string parent_name;
            if (auto s = vpi_get_str(vpiName, parent_h)) parent_name = s;
            sanitize_str(parent_name);
            fromNode = new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT,
                                       parent_name, nullptr, nullptr);
        }
        return new AstSelExtract(new FileLine("uhdm"), fromNode, msbNode, lsbNode);
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
        std::string parent_name = vpi_get_str(vpiName, parent_h);
        sanitize_str(parent_name);
        fromNode = new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT, parent_name,
                                   nullptr, nullptr);

        auto type = vpi_get(vpiIndexedPartSelectType, obj_h);
        if (type == vpiPosIndexed) {
            return new AstSelPlus(new FileLine("uhdm"), fromNode, bit, width);
        } else if (type == vpiNegIndexed) {
            return new AstSelMinus(new FileLine("uhdm"), fromNode, bit, width);
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
        AstNode* loop = new AstWhile(new FileLine("uhdm"), condp, bodysp, incsp);
        initsp->addNextNull(loop);
        AstNode* stmt = new AstBegin(new FileLine("uhdm"), "", initsp);
        return stmt;
    }
    case vpiDoWhile:
    case vpiWhile: {
        AstNode* condp = nullptr;
        AstNode* bodysp = nullptr;
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
                vpiStmt,
            },
            obj_h, shared, [&](AstNode* item) {
                if (bodysp == nullptr) {
                    bodysp = item;
                } else {
                    bodysp->addNextNull(item);
                }
            });
        AstNode* loop = new AstWhile(new FileLine("uhdm"), condp, bodysp);
        if (objectType == vpiWhile) {
            return loop;
        } else if (objectType == vpiDoWhile) {
            auto* first_iter = bodysp->cloneTree(true);
            first_iter->addNextNull(loop);
            return first_iter;
        }
        break;
    }

    case vpiBitTypespec: {
        AstRange* rangeNode = nullptr;
        visit_one_to_many({vpiRange}, obj_h, shared,
                          [&](AstNode* node) { rangeNode = reinterpret_cast<AstRange*>(node); });
        auto* dtype = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::BIT);
        dtype->rangep(rangeNode);
        return dtype;
    }
    case vpiLogicTypespec: {
        AstRange* rangeNode = nullptr;
        visit_one_to_many({vpiRange}, obj_h, shared,
                          [&](AstNode* node) { rangeNode = reinterpret_cast<AstRange*>(node); });
        auto* dtype = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::LOGIC);
        dtype->rangep(rangeNode);
        return dtype;
    }
    case vpiIntTypespec: {
        auto* name = vpi_get_str(vpiName, obj_h);
        if (name == nullptr) {
            auto* dtype = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::INT);
            return dtype;
        }
        return new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT, name, nullptr,
                               nullptr);
    }
    case vpiStringTypespec: {
        auto* dtype = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::STRING);
        return dtype;
    }
    case vpiIntegerTypespec: {
        AstNode* constNode = get_value_as_node(obj_h);
        if (constNode == nullptr) {
            v3info("Valueless typepec, returning dtype");
            auto* dtype = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::INTEGER);
            return dtype;
        }
        return constNode;
    }
    case vpiVoidTypespec: {
        return new AstVoidDType(new FileLine("uhdm"));
    }
    case vpiEnumTypespec: {
        const uhdm_handle* const handle = (const uhdm_handle*)obj_h;
        const UHDM::BaseClass* const object = (const UHDM::BaseClass*)handle->object;
        if (shared.visited_types.find(object) != shared.visited_types.end()) {
            // Already seen this, do not create a duplicate
            // References are handled using getDType, not in visit_object
            return nullptr;
        }

        shared.visited_types[object] = shared.package_prefix + objectName;

        AstNode* enum_members = nullptr;
        AstNodeDType* enum_member_dtype = nullptr;

        vpiHandle itr = vpi_iterate(vpiEnumConst, obj_h);
        while (vpiHandle item_h = vpi_scan(itr)) {
            auto* value = get_value_as_node(item_h);
            std::string item_name;
            if (auto s = vpi_get_str(vpiName, item_h)) {
                item_name = s;
                sanitize_str(item_name);
            }
            auto* wrapped_item = new AstEnumItem(new FileLine("uhdm"), item_name, nullptr, value);
            if (enum_members == nullptr) {
                enum_members = wrapped_item;
            } else {
                enum_members->addNextNull(wrapped_item);
            }
        }
        vpi_free_object(itr);

        visit_one_to_one({vpiBaseTypespec}, obj_h, shared, [&](AstNode* item) {
            if (item != nullptr) { enum_member_dtype = reinterpret_cast<AstNodeDType*>(item); }
        });
        if (enum_member_dtype == nullptr) {
            // No data type specified, use default
            enum_member_dtype = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::INT);
        }
        auto* enum_dtype = new AstEnumDType(new FileLine("uhdm"), VFlagChildDType(),
                                            enum_member_dtype, enum_members);
        auto* dtype = new AstDefImplicitDType(new FileLine("uhdm"), objectName, nullptr,
                                              VFlagChildDType(), enum_dtype);
        auto* enum_type
            = new AstTypedef(new FileLine("uhdm"), objectName, nullptr, VFlagChildDType(), dtype);
        shared.m_symp->reinsert(enum_type);
        return enum_type;
    }
    case vpiStructTypespec: {
        const uhdm_handle* const handle = (const uhdm_handle*)obj_h;
        const UHDM::BaseClass* const object = (const UHDM::BaseClass*)handle->object;
        if (shared.visited_types.find(object) != shared.visited_types.end()) {
            UINFO(6, "Object " << objectName << " was already visited" << std::endl);
            return node;
        }
        shared.visited_types[object] = shared.package_prefix + objectName;
        // VSigning below is used in AstStructDtype to indicate
        // if packed or not
        VSigning packed;
        if (vpi_get(vpiPacked, obj_h)) {
            packed = VSigning::SIGNED;
        } else {
            packed = VSigning::UNSIGNED;
        }
        auto* struct_dtype = new AstStructDType(new FileLine("uhdm"), packed);
        visit_one_to_many({vpiTypespecMember}, obj_h, shared, [&](AstNode* item) {
            if (item != nullptr) { struct_dtype->addMembersp(item); }
        });
        auto* dtype = new AstDefImplicitDType(new FileLine("uhdm"), objectName, nullptr,
                                              VFlagChildDType(), struct_dtype);
        auto* struct_type
            = new AstTypedef(new FileLine("uhdm"), objectName, nullptr, VFlagChildDType(), dtype);
        shared.m_symp->reinsert(struct_type);
        return struct_type;
    }
    case vpiTypespecMember: {
        AstNodeDType* typespec = nullptr;
        auto typespec_h = vpi_handle(vpiTypespec, obj_h);
        typespec = getDType(typespec_h, shared);
        if (typespec != nullptr) {
            auto* member = new AstMemberDType(new FileLine("uhdm"), objectName, VFlagChildDType(),
                                              reinterpret_cast<AstNodeDType*>(typespec));
            return member;
        }
        return nullptr;
    }
    case vpiTypeParameter: {
        AstNodeDType* dtype = nullptr;
        visit_one_to_one({vpiTypespec}, obj_h, shared, [&](AstNode* item) {
            if (item != nullptr) { dtype = reinterpret_cast<AstNodeDType*>(item); }
        });
        auto* ast_typedef
            = new AstTypedef(new FileLine("uhdm"), objectName, nullptr, VFlagChildDType(), dtype);
        shared.m_symp->reinsert(ast_typedef);
        return ast_typedef;
    }
    case vpiLogicVar:
    case vpiStringVar:
    case vpiTimeVar:
    case vpiRealVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiIntegerVar:
    case vpiEnumVar:
    case vpiBitVar:
    case vpiByteVar: {
        AstNodeDType* dtype = getDType(obj_h, shared);
        auto* var = new AstVar(new FileLine("uhdm"), AstVarType::VAR, objectName,
                               VFlagChildDType(), dtype);
        visit_one_to_one({vpiExpr}, obj_h, shared, [&](AstNode* item) { var->valuep(item); });
        return var;
    }
    case vpiPackedArrayVar:
    case vpiArrayVar: {
        auto dtype = getDType(obj_h, shared);

        auto* var = new AstVar(new FileLine("uhdm"), AstVarType::VAR, objectName,
                               VFlagChildDType(), dtype);
        return var;
    }
    case vpiChandleVar: {
        auto* dtype = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::CHANDLE);
        auto* var = new AstVar(new FileLine("uhdm"), AstVarType::VAR, objectName,
                               VFlagChildDType(), dtype);
        return var;
    }
    case vpiGenScopeArray: {
        return process_genScopeArray(obj_h, shared);
    }
    case vpiGenScope: {
        AstNode* statements = nullptr;
        visit_one_to_many(
            {
                vpiTypedef,
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
                vpiParameter,
                vpiParamAssign,
                vpiGenScopeArray,
                vpiProgram,
                vpiProgramArray,
                // vpiAssertion,
                vpiInterface,
                vpiInterfaceArray,
                vpiAliasStmt,
                vpiClockingBlock,
            },
            obj_h, shared, [&](AstNode* item) {
                if (statements == nullptr) {
                    statements = item;
                } else {
                    statements->addNextNull(item);
                }
            });
        return statements;
    }
    case vpiDelayControl: {
        s_vpi_delay delay;
        vpi_get_delays(obj_h, &delay);

        // Verilator ignores delay statements, just grab the first one for simplicity
        if (delay.da != nullptr) {
            auto* delay_c = new AstConst(new FileLine("uhdm"), delay.da[0].real);
            return new AstDelay(new FileLine("uhdm"), delay_c);
        }
    }
    case vpiBreak: {
        return new AstBreak(new FileLine("uhdm"));
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
        return new AstForeach(new FileLine("uhdm"), arrayp, bodyp);
    }
    case vpiMethodFuncCall: {
        AstNode* from = nullptr;
        AstNode* args = nullptr;
        visit_one_to_one({vpiPrefix}, obj_h, shared, [&](AstNode* item) { from = item; });
        if (from == nullptr) {
            from = new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT, "this",
                                   nullptr, nullptr);
        }
        visit_one_to_many({vpiArgument}, obj_h, shared, [&](AstNode* item) {
            if (args == nullptr) {
                args = item;
            } else {
                args->addNextNull(item);
            }
        });
        return new AstMethodCall(new FileLine("uhdm"), from, objectName, args);
    }
    // What we can see (but don't support yet)
    case vpiClassObj: break;
    case vpiClassDefn: {
        auto* definition = new AstClass(new FileLine("uhdm"), objectName);
        visit_one_to_many(
            {
                vpiTypedef,
                vpiVariables,
                // vpiMethods,  // Not supported yet in UHDM
                vpiConstraint,
                vpiParameter,
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
                assert = new AstAssert(new FileLine("uhdm"), item, nullptr, nullptr, true);
            }
        });
        return assert;
    }
    case vpiUnsupportedTypespec: {
        v3info("\t! This typespec is unsupported in UHDM: " << file_name << ":" << currentLine);
        // Create a reference and try to resolve later
        return new AstParseRef(new FileLine("uhdm"), VParseRefExp::en::PX_TEXT, objectName,
                               nullptr, nullptr);
    }
    case vpiUnsupportedStmt:
        v3info("\t! This statement is unsupported in UHDM: " << file_name << ":" << currentLine);
        // Dummy statement to keep parsing
        return new AstTime(new FileLine("uhdm"),
                           VTimescale::TS_1PS);  // TODO: revisit once we have it in UHDM
        break;
    case vpiUnsupportedExpr:
        v3info("\t! This expression is unsupported in UHDM: " << file_name << ":" << currentLine);
        // Dummy expression to keep parsing
        return new AstConst(new FileLine("uhdm"), 1);
        break;
    default: {
        // Notify we have something unhandled
        v3error("\t! Unhandled type: " << objectType << ":" << UHDM::VpiTypeName(obj_h));
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
    }
    std::vector<AstNodeModule*> nodes;
    for (auto node : shared.top_nodes) nodes.push_back(node.second);
    if (class_package != nullptr) { nodes.push_back(class_package); }
    return nodes;
}

}  // namespace UhdmAst
