
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

    if (objectType == vpiDesign) {
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
    else if (objectType == vpiClassObj) {
    }
    else if (objectType == vpiPort) {
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
    }
    else if (objectType == vpiPackage) {
    }
    else if (objectType == vpiClassDefn) {
    }
    else if (objectType == vpiModule) {
      std::cout << "> Is a module" << std::endl;
      AstModule *module = new AstModule(new FileLine("uhdm"), objectName);

      if (module != nullptr) {
        std::cout << "> Have node" << std::endl;
        itr = vpi_iterate(vpiPort, obj_h);
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
        return module;
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
