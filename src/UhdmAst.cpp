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
          std::vector<int> module_child_nodes = {vpiPort, vpiContAssign};
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
          // Look ahead: is it just a reference?
          const unsigned int rvalueType = vpi_get(vpiType, itr);
          if (rvalueType == vpiRefObj) {
            // If so, construct it here without visiting
            rvalue = new AstVarRef(new FileLine("uhdm"),
                                   vpi_get_str(vpiName, itr),
                                   false); // is lvalue
          } else {
            // Determine type as usual
            rvalue = visit_object(itr);
          }
        }
        vpi_free_object(itr);

        // Left
        itr = vpi_handle(vpiLhs,obj_h);
        if (itr) {
          // Look ahead: is it just a reference?
          const unsigned int lvalueType = vpi_get(vpiType, itr);
          if (lvalueType == vpiRefObj) {
            // If so, construct it here without visiting
            lvalue = new AstVarRef(new FileLine("uhdm"),
                                   vpi_get_str(vpiName, itr),
                                   true); // is lvalue
          } else {
            // Determine type as usual
            lvalue = visit_object(itr);
          }
        }
        vpi_free_object(itr);

        if (lvalue && rvalue) {
          return new AstAssignW(new FileLine("uhdm"), lvalue, rvalue);
        }
        break;
      }
      case vpiRefObj: {

        // TODO: We actually don't know if this is an lvalue below,
        // can it be read via vpi?
        node = new AstVarRef(new FileLine("uhdm"), objectName, false);
        return node;

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
