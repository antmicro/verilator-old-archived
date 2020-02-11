
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
  AstNodeModule* visit_object (vpiHandle obj_h) {
    std::cout << __FUNCTION__ << " " << obj_h << std::endl;
    // Will keep current node
    AstNodeModule* node = nullptr;

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
    }
    else if (objectType == vpiPackage) {
    }
    else if (objectType == vpiClassDefn) {
    }
    else if (objectType == vpiModule) {
      std::cout << "> Is a module" << std::endl;
      node = new AstModule(new FileLine("uhdm"), objectName);
    }

    if (node != nullptr) {
      std::cout << "> Have node" << std::endl;
      itr = vpi_iterate(vpiPort, obj_h);
      while (vpiHandle vpi_child_obj = vpi_scan(itr) ) {
        auto *childNode = visit_object(vpi_child_obj);
        std::cout << "! Out of general children" << std::endl;
        if (childNode != nullptr) {
          std::cout << ">> Has a child node" << std::endl;
          // Update current module's list of statements
          node->addStmtp(childNode);
        }
        vpi_free_object(vpi_child_obj);
      }
      vpi_free_object(itr);
      return node;
    }
    return nullptr;
  }

  std::vector<AstNodeModule*> visit_designs (const std::vector<vpiHandle>& designs) {
    std::cout << __FUNCTION__ << std::endl;
    std::vector<AstNodeModule*> nodes;
    for (auto design : designs) {
      nodes.push_back(visit_object(design));
    }
    return nodes;
  }

}
