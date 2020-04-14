#include <vector>
#include <functional>
#include <algorithm>

#include "headers/uhdm.h"

#include "V3Ast.h"
#include "UhdmAst.h"

namespace UhdmAst {

  // Walks through one-to-many relationships from given parent
  // node through the VPI interface, visiting child nodes belonging to
  // ChildrenNodeTypes that are present in the given object.
  void visit_one_to_many (const std::vector<int> childrenNodeTypes,
                          vpiHandle parentHandle,
                          std::set<const UHDM::BaseClass*> visited,
                          std::map<std::string, AstNodeModule*>* top_nodes,
                          const std::function<void(AstNode*)> &f) {
    for (auto child : childrenNodeTypes) {
      vpiHandle itr = vpi_iterate(child, parentHandle);
      while (vpiHandle vpi_child_obj = vpi_scan(itr) ) {
        auto *childNode = visit_object(vpi_child_obj, visited, top_nodes);
        f(childNode);
        vpi_free_object(vpi_child_obj);
      }
      vpi_free_object(itr);
    }
  }

  // Walks through one-to-one relationships from given parent
  // node through the VPI interface, visiting child nodes belonging to
  // ChildrenNodeTypes that are present in the given object.
  void visit_one_to_one (const std::vector<int> childrenNodeTypes,
                         vpiHandle parentHandle,
                         std::set<const UHDM::BaseClass*> visited,
                         std::map<std::string, AstNodeModule*>* top_nodes,
                         const std::function<void(AstNode*)> &f) {
    for (auto child : childrenNodeTypes) {
      vpiHandle itr = vpi_handle(child, parentHandle);
      if (itr) {
        auto *childNode = visit_object(itr, visited, top_nodes);
        f(childNode);
      }
      vpi_free_object(itr);
    }
  }

  void sanitize_str(std::string &s) {
    std::replace(s.begin(), s.end(), '@','_');
  }

  AstNode* visit_object (vpiHandle obj_h,
        std::set<const UHDM::BaseClass*> visited,
        std::map<std::string, AstNodeModule*>* top_nodes) {
    // Will keep current node
    AstNode* node = nullptr;

    // Current object data
    int lineNo = 0;
    std::string objectName = "";

    // For iterating over child objects
    vpiHandle itr;

    for (auto name : {vpiName, vpiFullName, vpiDefName}) {
      if (auto s = vpi_get_str(name, obj_h)) {
        objectName = s;
        sanitize_str(objectName);
        break;
      }
    }
    if (unsigned int l = vpi_get(vpiLineNo, obj_h)) {
      lineNo = l;
    }

    const unsigned int objectType = vpi_get(vpiType, obj_h);
    std::cout << "Object: " << objectName
              << " of type " << objectType
              << std::endl;
    bool alreadyVisited = false;
    const uhdm_handle* const handle = (const uhdm_handle*) obj_h;
    const UHDM::BaseClass* const object = (const UHDM::BaseClass*) handle->object;
    if (visited.find(object) != visited.end()) {
      alreadyVisited = true;
    }
    visited.insert(object);
    if (alreadyVisited) {
      return node;
    }

    switch(objectType) {
      case vpiDesign: {

        visit_one_to_many({UHDM::uhdmallInterfaces, UHDM::uhdmtopModules},
            obj_h,
            visited,
            top_nodes,
            [&](AstNode* module) {
              if (module != nullptr) {
                node = module;
              }
            });
        return node;
        // Unhandled relationships: will visit (and print) the object
        //visit_one_to_many({UHDM::uhdmtopModules,
        //                   UHDM::uhdmallPrograms,
        //                   UHDM::uhdmallPackages,
        //                   UHDM::uhdmallClasses,
        //                   UHDM::uhdmallInterfaces,
        //                   UHDM::uhdmallUdps},
        //                  obj_h,
        //                  visited,
        //                  [](AstNode* node){});

      }
      case vpiPort: {
        static unsigned numPorts;
        AstPort *port = nullptr;
        AstVar *var = nullptr;
        AstNodeDType *dtype = nullptr;

        // Get actual type
        vpiHandle lowConn_h = vpi_handle(vpiLowConn, obj_h);
        if (lowConn_h != nullptr) {
          vpiHandle actual_h = vpi_handle(vpiActual, lowConn_h);
          auto actual_type = vpi_get(vpiType, actual_h);
          if (actual_type == vpiModport) {
            vpiHandle iface_h = vpi_handle(vpiInterface, actual_h);

            std::string cellName, ifaceName;
            if (auto s = vpi_get_str(vpiName, actual_h)) {
              cellName = s;
              sanitize_str(cellName);
            }
            if (auto s = vpi_get_str(vpiDefName, iface_h)) {
              ifaceName = s;
              sanitize_str(ifaceName);
            }
            dtype = new AstIfaceRefDType(new FileLine("uhdm"),
                                         cellName,
                                         ifaceName);
            var = new AstVar(new FileLine("uhdm"),
                             AstVarType::IFACEREF,
                             objectName,
                             dtype);
            port = new AstPort(new FileLine("uhdm"), ++numPorts, objectName);
            port->addNextNull(var);
            var->childDTypep(dtype);
            return port;
          }
        }
        dtype = new AstBasicDType(new FileLine("uhdm"),
                                  AstBasicDTypeKwd::LOGIC_IMPLICIT);
        var = new AstVar(new FileLine("uhdm"),
                         AstVarType::PORT,
                         objectName,
                         dtype);

        if (const int n = vpi_get(vpiDirection, obj_h)) {
          if (n == vpiInput) {
            var->declDirection(VDirection::INPUT);
            var->direction(VDirection::INPUT);
            var->varType(AstVarType::WIRE);
          } else if (n == vpiOutput) {
            var->declDirection(VDirection::OUTPUT);
            var->direction(VDirection::OUTPUT);
          } else if (n == vpiInout) {
            var->declDirection(VDirection::INOUT);
            var->direction(VDirection::INOUT);
          }
        }

        port = new AstPort(new FileLine("uhdm"), ++numPorts, objectName);
        port->addNextNull(var);
        var->childDTypep(dtype);

        if (v3Global.opt.trace()) {
            var->trace(true);
        }

        if (port) {
          return port;
        }
        // Unhandled relationships: will visit (and print) the object
        //visit_one_to_many({vpiBit},
        //                  obj_h,
        //                  visited,
        //                  [](AstNode*){});
        //visit_one_to_one({vpiTypedef,
        //                  vpiInstance,
        //                  vpiModule,
        //                  vpiHighConn,
        //                  vpiLowConn},
        //                 obj_h,
        //                 visited,
        //                 [](AstNode*){});

        break;
      }
      case vpiModule: {

        std::string modType = vpi_get_str(vpiDefName, obj_h);
        sanitize_str(modType);

        AstModule *module;

        // Check if we have encountered this object before
        auto it = top_nodes->find(modType);
        if (it != top_nodes->end()) {
          // Was created before, fill missing
          module = reinterpret_cast<AstModule*>(it->second);
          visit_one_to_many({
              vpiInterface,
              vpiModule,
              vpiContAssign,
              },
              obj_h,
              visited,
              top_nodes,
              [&](AstNode* node){
                if (node != nullptr)
                  module->addStmtp(node);
              });
        } else {
          // Encountered for the first time
          module = new AstModule(new FileLine("uhdm"), modType);
          visit_one_to_many({
              vpiPort,
              vpiModule,
              vpiContAssign,
              },
              obj_h,
              visited,
              top_nodes,
              [&](AstNode* node){
                if (node != nullptr)
                  module->addStmtp(node);
              });
        }
        (*top_nodes)[module->name()] = module;

        if (objectName != modType) {
          // Not a top module, create instance
          AstPin *modPins = nullptr;
          AstPin *modParams = nullptr;

          // Get port assignments
          vpiHandle itr = vpi_iterate(vpiPort, obj_h);
          int np = 0;
          while (vpiHandle vpi_child_obj = vpi_scan(itr) ) {
            vpiHandle highConn = vpi_handle(vpiHighConn, vpi_child_obj);
            if (highConn) {
              std::string portName = vpi_get_str(vpiName, vpi_child_obj);
              sanitize_str(portName);
              AstParseRef *ref = reinterpret_cast<AstParseRef *>(visit_object(highConn, visited, top_nodes));
              AstPin *pin = new AstPin(new FileLine("uhdm"), ++np, portName, ref);
              if (!modPins)
                  modPins = pin;
              else
                  modPins->addNextNull(pin);
            }

            vpi_free_object(vpi_child_obj);
          }
          vpi_free_object(itr);

          std::string fullname = vpi_get_str(vpiFullName, obj_h);
          sanitize_str(fullname);
          AstCell *cell = new AstCell(new FileLine("uhdm"), new FileLine("uhdm"),
              objectName, modType, modPins, modParams, nullptr);
          return cell;
        }
        // Unhandled relationships: will visit (and print) the object
        //visit_one_to_many({vpiProcess,
        //                   vpiPrimitive,
        //                   vpiPrimitiveArray,
        //                   vpiInterface,
        //                   vpiInterfaceArray,
        //                   vpiModule,
        //                   vpiModuleArray,
        //                   vpiModPath,
        //                   vpiTchk,
        //                   vpiDefParam,
        //                   vpiIODecl,
        //                   vpiAliasStmt,
        //                   vpiClockingBlock,
        //                   vpiTaskFunc,
        //                   vpiNet,
        //                   vpiArrayNet,
        //                   vpiAssertion,
        //                   vpiClassDefn,
        //                   vpiProgram,
        //                   vpiProgramArray,
        //                   vpiSpecParam,
        //                   vpiConcurrentAssertions,
        //                   vpiVariables,
        //                   vpiParameter,
        //                   vpiInternalScope,
        //                   vpiTypedef,
        //                   vpiPropertyDecl,
        //                   vpiSequenceDecl,
        //                   vpiNamedEvent,
        //                   vpiNamedEventArray,
        //                   vpiVirtualInterfaceVar,
        //                   vpiReg,
        //                   vpiRegArray,
        //                   vpiMemory,
        //                   vpiLetDecl,
        //                   vpiImport
        //                  },
        //                  obj_h,
        //                  visited,
        //                  [](AstNode* node){});
        //visit_one_to_one({vpiDefaultDisableIff,
        //                  vpiInstanceArray,
        //                  vpiGlobalClocking,
        //                  vpiDefaultClocking,
        //                  vpiModuleArray,
        //                  vpiInstance,
        //                  vpiModule  // TODO: Both here and in one-to-many?
        //                 },
        //                 obj_h,
        //                 visited,
        //                 [](AstNode*){});

        break;
      }
      case vpiContAssign: {
        AstNode* lvalue = nullptr;
        AstNode* rvalue = nullptr;

        // Right
        visit_one_to_one({vpiRhs},
            obj_h,
            visited,
            top_nodes,
            [&](AstNode* child){
              rvalue = child;
            });

        // Left
        visit_one_to_one({vpiLhs},
            obj_h,
            visited,
            top_nodes,
            [&](AstNode* child){
              lvalue = child;
            });

        if (lvalue && rvalue) {
          return new AstAssignW(new FileLine("uhdm"), lvalue, rvalue);
        }
        // Unhandled relationships: will visit (and print) the object
        //visit_one_to_one({vpiDelay},
        //                 obj_h,
        //                 visited,
        //                 [](AstNode*){});
        //visit_one_to_many({vpiBit},
        //                  obj_h,
        //                  visited,
        //                  [](AstNode*){});

        break;
      }
      case vpiRefObj: {
        size_t dot_pos = objectName.rfind('.');
        if (dot_pos != std::string::npos) {
          //TODO: Handle >1 dot
          std::string lhs = objectName.substr(0, dot_pos);
          std::string rhs = objectName.substr(dot_pos + 1, objectName.length());
          AstParseRef* lhsNode = new AstParseRef(new FileLine("uhdm"),
                                                 AstParseRefExp::en::PX_TEXT,
                                                 lhs,
                                                 nullptr,
                                                 nullptr);
          AstParseRef* rhsNode = new AstParseRef(new FileLine("uhdm"),
                                                 AstParseRefExp::en::PX_TEXT,
                                                 rhs,
                                                 nullptr,
                                                 nullptr);

          return new AstDot(new FileLine("uhdm"), lhsNode, rhsNode);
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
          return new AstParseRef(new FileLine("uhdm"),
                                                 AstParseRefExp::en::PX_TEXT,
                                                 objectName,
                                                 nullptr,
                                                 nullptr);
        }

        // Unhandled relationships: will visit (and print) the object
        //visit_one_to_one({vpiInstance,
        //                  vpiTaskFunc,
        //                  vpiTypespec},
        //                 obj_h,
        //                 visited,
        //                 [](AstNode*){});
        //visit_one_to_many({vpiPortInst},
        //                  obj_h,
        //                  visited,
        //                  [](AstNode*){});

        break;
      }
      case vpiNet: {
        AstBasicDType *dtype = nullptr;
        //TODO: get type
        dtype = new AstBasicDType(new FileLine("uhdm"),
                                  AstBasicDTypeKwd::LOGIC_IMPLICIT);
        auto *v = new AstVar(new FileLine("uhdm"), AstVarType::WIRE, objectName, dtype);
        v->childDTypep(dtype);
        return v;

        // Unhandled relationships: will visit (and print) the object
        //visit_one_to_one({vpiLeftRange,
        //                  vpiRightRange,
        //                  vpiSimNet,
        //                  vpiModule,
        //                  vpiTypespec
        //                 },
        //                 obj_h,
        //                 visited,
        //                 [](AstNode*){});
        //visit_one_to_many({vpiRange,
        //                   vpiBit,
        //                   vpiPortInst,
        //                   vpiDriver,
        //                   vpiLoad,
        //                   vpiLocalDriver,
        //                   vpiLocalLoad,
        //                   vpiPrimTerm,
        //                   vpiContAssign,
        //                   vpiPathTerm,
        //                   vpiTchkTerm
        //                  },
        //                  obj_h,
        //                  visited,
        //                  [](AstNode*){});
        break;
      }
      case vpiClassDefn: {

        // Unhandled relationships: will visit (and print) the object
        //visit_one_to_many({vpiConcurrentAssertions,
        //                   vpiVariables,
        //                   vpiParameter,
        //                   vpiInternalScope,
        //                   vpiTypedef,
        //                   vpiPropertyDecl,
        //                   vpiSequenceDecl,
        //                   vpiNamedEvent,
        //                   vpiNamedEventArray,
        //                   vpiVirtualInterfaceVar,
        //                   vpiReg,
        //                   vpiRegArray,
        //                   vpiMemory,
        //                   vpiLetDecl,
        //                   vpiImport},
        //                  obj_h,
        //                  visited,
        //                  [](AstNode*){});

        break;
      }
      case vpiInterface: {
        // Interface definition is represented by a module node
        AstIface* elaboratedInterface = new AstIface(new FileLine("uhdm"), objectName);
        visit_one_to_many({
            vpiNet,
            vpiModport
            },
            obj_h,
            visited,
            top_nodes,
            [&](AstNode* port){
          if(port) {
            elaboratedInterface->addStmtp(port);
          }
        });
        elaboratedInterface->name(objectName);
        std::string modType = vpi_get_str(vpiDefName, obj_h);
        sanitize_str(modType);
        if (objectName != modType) {
          AstPin *modPins = nullptr;
          AstPin *modParams = nullptr;
          AstCell *cell = new AstCell(new FileLine("uhdm"), new FileLine("uhdm"),
              objectName, modType, modPins, modParams, nullptr);
          return cell;
        } else {
          // is top level
          return elaboratedInterface;
        }
        // Unhandled relationships: will visit (and print) the object
        //visit_one_to_one({
        //    vpiParent,
        //    vpiInstanceArray,
        //    vpiGlobalClocking,
        //    vpiDefaultClocking,
        //    vpiDefaultDisableIff,
        //    vpiInstance,
        //    vpiModule
        //    },
        //    obj_h,
        //    visited,
        //    [](AST::AstNode*){});
        //visit_one_to_many({
        //    vpiProcess,
        //    vpiInterfaceTfDecl,
        //    vpiModPath,
        //    vpiContAssign,
        //    vpiInterface,
        //    vpiInterfaceArray,
        //    vpiPort,
        //    vpiTaskFunc,
        //    vpiArrayNet,
        //    vpiAssertion,
        //    vpiClassDefn,
        //    vpiProgram,
        //    vpiProgramArray,
        //    vpiSpecParam,
        //    vpiConcurrentAssertions,
        //    vpiVariables,
        //    vpiParameter,
        //    vpiInternalScope,
        //    vpiTypedef,
        //    vpiPropertyDecl,
        //    vpiSequenceDecl,
        //    vpiNamedEvent,
        //    vpiNamedEventArray,
        //    vpiVirtualInterfaceVar,
        //    vpiReg,
        //    vpiRegArray,
        //    vpiMemory,
        //    vpiLetDecl,
        //    vpiImport,
        //    },
        //    obj_h,
        //    visited,
        //    [](AST::AstNode*){});
        break;
      }
      case vpiModport: {
        AstNode* modport_vars = nullptr;
        visit_one_to_many({vpiIODecl},
            obj_h,
            visited,
            top_nodes,
            [&](AstNode* net){
          if(net) {
            if (modport_vars == nullptr) {
              modport_vars = net;
            } else {
              modport_vars->addNext(net);
            }
          }
        });
        AstModport *node = new AstModport(new FileLine("uhdm"), objectName, modport_vars);
        return node;
      }
      case vpiIODecl: {
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
        AstModportVarRef* io_node = new AstModportVarRef(new FileLine("uhdm"), objectName, dir);
        return io_node;
      }
      // What we can see (but don't support yet)
      case vpiClassObj:
      case vpiPackage:
      default: {
        break;
      }
    }

    return nullptr;
  }

  std::vector<AstNodeModule*> visit_designs (const std::vector<vpiHandle>& designs) {
    std::set<const UHDM::BaseClass*> visited;
    std::map<std::string, AstNodeModule*> top_nodes;
    for (auto design : designs) {
        visit_one_to_many({
            UHDM::uhdmallInterfaces,
            UHDM::uhdmallModules,
            UHDM::uhdmtopModules
            },
            design,
            visited,
            &top_nodes,
            [&](AstNode* module) {
              if (module != nullptr) {
              // Top level nodes need to be NodeModules (created from design)
              // This is true as we visit only top modules and interfaces (with the same AST node) above
              top_nodes[module->name()] = (reinterpret_cast<AstNodeModule*>(module));
              }
            });
    }
    std::vector<AstNodeModule*> nodes;
    for (auto node : top_nodes)
              nodes.push_back(node.second);
    return nodes;
  }

}
