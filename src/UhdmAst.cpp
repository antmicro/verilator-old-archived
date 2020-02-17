#include <vector>

#include "headers/uhdm.h"

#include "V3Ast.h"

namespace UhdmAst {
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

    switch(objectType) {
      case vpiDesign: {
        //FIXME: Only one module for now
        itr = vpi_iterate(UHDM::uhdmallModules,obj_h);
        while (vpiHandle vpi_obj = vpi_scan(itr) ) {
          node = visit_object(vpi_obj);
          vpi_free_object(vpi_obj);
        }
        vpi_free_object(itr);
        return node;
      }
      case vpiPort: {
        static unsigned numPorts;
        AstPort *port = nullptr;
        AstVar *var = nullptr;
        AstBasicDType *dtype = nullptr;

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

        if (module != nullptr) {
          std::vector<int> module_child_nodes = {vpiPort,
                                                 vpiContAssign,
                                                 vpiLogicNet};
          for (auto child : module_child_nodes) {
            itr = vpi_iterate(child, obj_h);
            while (vpiHandle vpi_child_obj = vpi_scan(itr) ) {
              auto *childNode = visit_object(vpi_child_obj);
              if (childNode != nullptr) {
                // Update current module's list of statements
                module->addStmtp(childNode);
              }
              vpi_free_object(vpi_child_obj);
            }
            vpi_free_object(itr);
          }
          return module;
        }
        break;
      }
      case vpiContAssign: {
        AstNode* lvalue = nullptr;
        AstNode* rvalue = nullptr;

        // Right
        itr = vpi_handle(vpiRhs,obj_h);
        if (itr) {
          rvalue = visit_object(itr);
        }
        vpi_free_object(itr);

        // Left
        itr = vpi_handle(vpiLhs,obj_h);
        if (itr) {
          lvalue = visit_object(itr);
        }
        vpi_free_object(itr);

        if (lvalue && rvalue) {
          return new AstAssignW(new FileLine("uhdm"), lvalue, rvalue);
        }
        break;
      }
      case vpiRefObj: {
        bool isLvalue = false;
        std::vector<int> child_node_handle_types = {vpiInstance,
                                                    vpiTaskFunc,
                                                    vpiTypespec};
        std::vector<int> child_node_iter_types = {vpiPortInst};
        for (auto child : child_node_handle_types) {
          itr = vpi_handle(child,obj_h);
          if (itr){
            auto *childNode = visit_object(itr);
          }
          vpi_free_object(itr);
        }
        for (auto child : child_node_iter_types) {
          itr = vpi_iterate(child, obj_h);
          while (vpiHandle vpi_child_obj = vpi_scan(itr) ) {
            auto *childNode = visit_object(vpi_child_obj);
            vpi_free_object(vpi_child_obj);
          }
          vpi_free_object(itr);
        }

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
        std::cout << "Got a logicNet" << std::endl;
          std::vector<int> child_node_handle_types = {vpiLeftRange,
                                                      vpiRightRange,
                                                      };
          std::vector<int> child_node_iter_types = {vpiRange,
                                                    vpiBit};
          for (auto child : child_node_handle_types) {
            itr = vpi_handle(child,obj_h);
            if (itr){
        std::cout << "Got a handle" << std::endl;
              auto *childNode = visit_object(itr);
            }
            vpi_free_object(itr);
          }
          for (auto child : child_node_iter_types) {
            itr = vpi_iterate(child, obj_h);
            while (vpiHandle vpi_child_obj = vpi_scan(itr) ) {
        std::cout << "Got an iterator" << std::endl;
              auto *childNode = visit_object(vpi_child_obj);
              vpi_free_object(vpi_child_obj);
            }
            vpi_free_object(itr);
          }
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
      // What we can see (but don't support yet)
      case vpiClassObj:
      case vpiPackage:
      case vpiClassDefn:
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
