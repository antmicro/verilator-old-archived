
#include <string.h>

#include <iostream>
#include <map>
#include <string>
#include <vector>

#include "include/sv_vpi_user.h"
#include "include/vhpi_user.h"

#include "headers/uhdm_types.h"
#include "headers/containers.h"
#include "headers/vpi_uhdm.h"
#include "headers/uhdm.h"
#include "headers/Serializer.h"

#include "V3Ast.h"

namespace UhdmAst {
  AstNode* visit_object (vpiHandle obj_h) {
    std::cout << __FUNCTION__ << " " << obj_h << std::endl;
    // Will keep current node
    AstNode* node = nullptr;

    static unsigned numPorts;
    // Current object data
    int lineNo = 0;
    std::string objectName = "";

    // For iterating over child objects
    vpiHandle itr;

    if (const char* s = vpi_get_str(vpiName, obj_h)) {
      objectName = s;
      std::cout << "> name: " << objectName << std::endl;
    }
    if (unsigned int l = vpi_get(vpiLineNo, obj_h)) {
      lineNo = l;
      std::cout << "> line: " << lineNo << std::endl;
    }

    const unsigned int objectType = vpi_get(vpiType, obj_h);
    std::cout << "> type: " << objectType << std::endl;

    switch(objectType) {
      case vpiDesign: {
        std::cout << "> Is a design" << std::endl;
        itr = vpi_iterate(UHDM::uhdmallModules,obj_h);
        while (vpiHandle vpi_obj = vpi_scan(itr) ) {
          node = visit_object(vpi_obj);
          std::cout << "! Out of design children" << std::endl;
          vpi_free_object(vpi_obj);
        }
        vpi_free_object(itr);
        return node;
      }
      case vpiClassObj: {
        std::cout << "> Is a ClassObj" << std::endl;
        break;
      }
      case vpiPort: {
        std::cout << "> Is a port" << std::endl;
        AstPort *port = nullptr;
        AstVar *var = nullptr;
        AstBasicDType *dtype = nullptr;

        dtype = new AstBasicDType(new FileLine("uhdm"), AstBasicDTypeKwd::LOGIC_IMPLICIT);

        port = new AstPort(new FileLine("uhdm"), ++numPorts, objectName);

        var = new AstVar(new FileLine("uhdm"), AstVarType::PORT, objectName, dtype);
        if (const int n = vpi_get(vpiDirection, obj_h)) {
          if (n == 1) {
            var->declDirection(VDirection::INPUT);
            var->direction(VDirection::INPUT);
          } else if (n == 2) {
            var->declDirection(VDirection::OUTPUT);
            var->direction(VDirection::OUTPUT);
          }
        }

        port->addNextNull(var);
        var->childDTypep(dtype);

        //if (v3Global.opt.trace())
        //    var->trace(true);

        if (port) {
          return port;
        }
        break;
      }
      case vpiPackage: {
        std::cout << "> Is a package" << std::endl;
        break;
      }
      case vpiClassDefn: {
        std::cout << "> Is a ClassDefn" << std::endl;
        break;
      }
      case vpiModule: {
        std::cout << "> Is a module" << std::endl;
        AstModule *module = new AstModule(new FileLine("uhdm"), objectName);

        if (module != nullptr) {
          std::cout << "> Have node" << std::endl;

          std::vector<int> module_child_nodes = {vpiPort, vpiContAssign};
          for (auto child : module_child_nodes) {
            itr = vpi_iterate(child, obj_h);
            while (vpiHandle vpi_child_obj = vpi_scan(itr) ) {
              auto *childNode = visit_object(vpi_child_obj);
              std::cout << "! Out of general children" << std::endl;
              if (childNode != nullptr) {
                std::cout << ">> Has a child node" << std::endl;
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
        std::cout << ">> Is a ContAssign" << std::endl;
        AstNode* lvalue = nullptr;
        AstNode* rvalue = nullptr;

        // Right
        itr = vpi_handle(vpiRhs,obj_h);
        if (itr) {
          std::cout << ">> have right" << std::endl;
          rvalue = visit_object(itr);
        }
        vpi_free_object(itr);

        // Left
        itr = vpi_handle(vpiLhs,obj_h);
        if (itr) {
          std::cout << ">> have left" << std::endl;
          lvalue = visit_object(itr);
        }
        vpi_free_object(itr);

        if (lvalue && rvalue) {
          std::cout << ">> returning contAssign" << std::endl;
          return new AstAssignW(new FileLine("uhdm"), lvalue, rvalue);
        }
        break;
      }
      default: {
        break;
      }
    }

    return nullptr;
  }

  std::vector<AstNodeModule*> visit_designs (const std::vector<vpiHandle>& designs) {
    std::cout << __FUNCTION__ << std::endl;
    std::vector<AstNodeModule*> nodes;
    for (auto design : designs) {
      // Top level nodes need to be NodeModules (created from design)
      nodes.push_back(reinterpret_cast<AstNodeModule*>(visit_object(design)));
    }
    std::cout << __FUNCTION__ << " end" << std::endl;
    return nodes;
  }

}
