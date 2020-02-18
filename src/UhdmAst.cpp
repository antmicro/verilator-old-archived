#include <vector>
#include <functional>

#include "headers/uhdm.h"

#include "V3Ast.h"
#include "UhdmAst.h"

namespace UhdmAst {

  // Walks through one-to-many relationships from given parent
  // node through the VPI interface, visiting child nodes belonging to
  // ChildrenNodeTypes that are present in the given object.
  void visit_one_to_many (const std::vector<int> childrenNodeTypes,
                          vpiHandle parentHandle,
                          const std::function<void(AstNode*)> &f) {
    for (auto child : childrenNodeTypes) {
      vpiHandle itr = vpi_iterate(child, parentHandle);
      while (vpiHandle vpi_child_obj = vpi_scan(itr) ) {
        auto *childNode = visit_object(vpi_child_obj);
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
                          const std::function<void(AstNode*)> &f) {
    for (auto child : childrenNodeTypes) {
      vpiHandle itr = vpi_handle(child, parentHandle);
      if (itr) {
        auto *childNode = visit_object(itr);
        f(childNode);
      }
      vpi_free_object(itr);
    }
  }

  AstNode* visit_object (vpiHandle obj_h) {
    // Will keep current node
    AstNode* node = nullptr;

    // Current object data
    int lineNo = 0;
    std::string objectName = "";

    // For iterating over child objects
    vpiHandle itr;

    if (const char* s = vpi_get_str(vpiName, obj_h)) {
      objectName = s;
    }
    if (unsigned int l = vpi_get(vpiLineNo, obj_h)) {
      lineNo = l;
    }

    const unsigned int objectType = vpi_get(vpiType, obj_h);
    std::cout << "Object: " << objectName
              << " of type " << objectType
              << std::endl;

    switch(objectType) {
      case vpiDesign: {

        // Unhandled relationships: will visit (and print) the object
        visit_one_to_many({UHDM::uhdmtopModules,
                           UHDM::uhdmallPrograms,
                           UHDM::uhdmallPackages,
                           UHDM::uhdmallClasses,
                           UHDM::uhdmallInterfaces,
                           UHDM::uhdmallUdps},
                          obj_h,
                          [](AstNode* node){});

        //FIXME: Only one module for now
        visit_one_to_many({UHDM::uhdmallModules},
            obj_h,
            [&](AstNode* module) {
              if (module != nullptr) {
                node = module;
              }
            });

        return node;
      }
      case vpiPort: {
        static unsigned numPorts;
        AstPort *port = nullptr;
        AstVar *var = nullptr;
        AstBasicDType *dtype = nullptr;

        // Unhandled relationships: will visit (and print) the object
        visit_one_to_many({vpiBit},
                          obj_h,
                          [](AstNode*){});
        visit_one_to_one({vpiTypedef,
                          vpiInstance,
                          vpiModule,
                          vpiHighConn,
                          vpiLowConn},
                         obj_h,
                         [](AstNode*){});

        dtype = new AstBasicDType(new FileLine("uhdm"),
                                  AstBasicDTypeKwd::LOGIC_IMPLICIT);
        port = new AstPort(new FileLine("uhdm"), ++numPorts, objectName);
        var = new AstVar(new FileLine("uhdm"),
                         AstVarType::PORT,
                         objectName,
                         dtype);

        if (const int n = vpi_get(vpiDirection, obj_h)) {
          if (n == vpiInput) {
            var->declDirection(VDirection::INPUT);
            var->direction(VDirection::INPUT);
          } else if (n == vpiOutput) {
            var->declDirection(VDirection::OUTPUT);
            var->direction(VDirection::OUTPUT);
          } else if (n == vpiInout) {
            var->declDirection(VDirection::INOUT);
            var->direction(VDirection::INOUT);
          }
        }

        port->addNextNull(var);
        var->childDTypep(dtype);

        if (v3Global.opt.trace()) {
            var->trace(true);
        }

        if (port) {
          return port;
        }
        break;
      }
      case vpiModule: {
        AstModule *module = new AstModule(new FileLine("uhdm"), objectName);

        // Unhandled relationships: will visit (and print) the object
        visit_one_to_many({vpiProcess,
                           vpiPrimitive,
                           vpiPrimitiveArray,
                           vpiInterface,
                           vpiInterfaceArray,
                           vpiModule,
                           vpiModuleArray,
                           vpiModPath,
                           vpiTchk,
                           vpiDefParam,
                           vpiIODecl,
                           vpiAliasStmt,
                           vpiClockingBlock,
                           vpiTaskFunc,
                           vpiNet,
                           vpiArrayNet,
                           vpiAssertion,
                           vpiClassDefn,
                           vpiProgram,
                           vpiProgramArray,
                           vpiSpecParam,
                           vpiConcurrentAssertions,
                           vpiVariables,
                           vpiParameter,
                           vpiInternalScope,
                           vpiTypedef,
                           vpiPropertyDecl,
                           vpiSequenceDecl,
                           vpiNamedEvent,
                           vpiNamedEventArray,
                           vpiVirtualInterfaceVar,
                           vpiReg,
                           vpiRegArray,
                           vpiMemory,
                           vpiLetDecl,
                           vpiImport
                          },
                          obj_h,
                          [](AstNode* node){});
        visit_one_to_one({vpiDefaultDisableIff,
                          vpiInstanceArray,
                          vpiGlobalClocking,
                          vpiDefaultClocking,
                          vpiModuleArray,
                          vpiInstance,
                          vpiModule  // TODO: Both here and in one-to-many?
                         },
                         obj_h,
                         [](AstNode*){});


        if (module != nullptr) {
          visit_one_to_many({vpiPort, vpiContAssign, vpiLogicNet},
              obj_h,
              [&](AstNode* node){
                if (node != nullptr)
                  module->addStmtp(node);
              });
          return module;
        }
        break;
      }
      case vpiContAssign: {
        AstNode* lvalue = nullptr;
        AstNode* rvalue = nullptr;

        // Unhandled relationships: will visit (and print) the object
        visit_one_to_one({vpiDelay},
                         obj_h,
                         [](AstNode*){});
        visit_one_to_many({vpiBit},
                          obj_h,
                          [](AstNode*){});

        // Right
        visit_one_to_one({vpiRhs},
            obj_h,
            [&](AstNode* child){
              rvalue = child;
            });

        // Left
        visit_one_to_one({vpiLhs},
            obj_h,
            [&](AstNode* child){
              lvalue = child;
            });

        if (lvalue && rvalue) {
          return new AstAssignW(new FileLine("uhdm"), lvalue, rvalue);
        }
        break;
      }
      case vpiRefObj: {
        bool isLvalue = false;
        // Unhandled relationships: will visit (and print) the object
        visit_one_to_one({vpiInstance,
                          vpiTaskFunc,
                          vpiTypespec},
                         obj_h,
                         [](AstNode*){});
        visit_one_to_many({vpiPortInst},
                          obj_h,
                          [](AstNode*){});

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
        node = new AstVarRef(new FileLine("uhdm"), objectName, isLvalue);
        return node;

        break;
      }
      case vpiLogicNet: {
        // Handling of this node is not functional yet
        break;
        // Unhandled relationships: will visit (and print) the object
        visit_one_to_one({vpiLeftRange,
                          vpiRightRange,
                          vpiSimNet,
                          vpiModule,
                          vpiTypespec
                         },
                         obj_h,
                         [](AstNode*){});
        visit_one_to_many({vpiRange,
                           vpiBit,
                           vpiPortInst,
                           vpiDriver,
                           vpiLoad,
                           vpiLocalDriver,
                           vpiLocalLoad,
                           vpiPrimTerm,
                           vpiContAssign,
                           vpiPathTerm,
                           vpiTchkTerm
                          },
                          obj_h,
                          [](AstNode*){});

        AstBasicDType *dtype = nullptr;
        dtype = new AstBasicDType(new FileLine("uhdm"),
                                  AstBasicDTypeKwd::LOGIC_IMPLICIT);
        if (const int n = vpi_get(vpiNetType, obj_h)) {
          std::cout << "Net type: " << n << std::endl;
        }
        auto *v = new AstVar(new FileLine("uhdm"), AstVarType::VAR, objectName, dtype);
        v->childDTypep(dtype);
        return v;

        break;
      }
      case vpiClassDefn: {
        if (const char* s = vpi_get_str(vpiFullName, obj_h)) {
          std::cout << "|vpiFullName: " << s << std::endl;
        }

        // Unhandled relationships: will visit (and print) the object
        visit_one_to_many({vpiConcurrentAssertions,
                           vpiVariables,
                           vpiParameter,
                           vpiInternalScope,
                           vpiTypedef,
                           vpiPropertyDecl,
                           vpiSequenceDecl,
                           vpiNamedEvent,
                           vpiNamedEventArray,
                           vpiVirtualInterfaceVar,
                           vpiReg,
                           vpiRegArray,
                           vpiMemory,
                           vpiLetDecl,
                           vpiImport},
                          obj_h,
                          [](AstNode*){});

        break;
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
    std::vector<AstNodeModule*> nodes;
    for (auto design : designs) {
      // Top level nodes need to be NodeModules (created from design)
      nodes.push_back(reinterpret_cast<AstNodeModule*>(visit_object(design)));
    }
    return nodes;
  }

}
