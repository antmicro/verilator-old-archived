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
          vpiHandle iface_h = nullptr;
          if (actual_type == vpiModport) {
            iface_h = vpi_handle(vpiInterface, actual_h);
          } else if (actual_type == vpiInterface) {
            iface_h = actual_h;
          }
          if (iface_h != nullptr) {
            // Only if was set above
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
              //vpiParamAssign,  - obtain value when visiting parameter below
              vpiParameter,
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
              vpiProcess,
              //vpiParameter,  - wait for instantiation to get the assigned value
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
        break;
      }
      case vpiAssignment:
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
          if (objectType == vpiAssignment)
            return new AstAssign(new FileLine("uhdm"), lvalue, rvalue);
          else if (objectType == vpiContAssign)
            return new AstAssignW(new FileLine("uhdm"), lvalue, rvalue);
        }
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
      }
      case vpiParameter: {
        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                                        AstBasicDTypeKwd::LOGIC_IMPLICIT);
        auto* parameter = new AstVar(new FileLine("uhdm"),
                               AstVarType::GPARAM,
                               objectName,
                               dtype);
        AstNode* parameter_value = nullptr;
        s_vpi_value val;
        vpi_get_value(obj_h, &val);
        switch (val.format) {
          case vpiIntVal: {
            parameter_value = new AstConst(new FileLine("uhdm"), AstConst::Unsized32(), (val.value.integer));
            break;
          }
          default: {
            std::cout << "\t! Encountered unhandled parameter value type" << std::endl;
            break;
          }
        }
        parameter->childDTypep(dtype);
        parameter->valuep(parameter_value);
        return parameter;
      }
      case vpiInterface: {
        // Interface definition is represented by a module node
        AstIface* elaboratedInterface = new AstIface(new FileLine("uhdm"), objectName);
        bool hasModports = false;
        visit_one_to_many({
            vpiPort,
            vpiParameter,
            },
            obj_h,
            visited,
            top_nodes,
            [&](AstNode* port){
          if(port) {
            elaboratedInterface->addStmtp(port);
          }
        });
        visit_one_to_many({vpiModport}, obj_h, visited, top_nodes, [&](AstNode* port){
          if(port) {
            hasModports = true;
            elaboratedInterface->addStmtp(port);
          }
        });
        if (hasModports) {
          // Only then create the nets, as they won't be connected otherwise
          visit_one_to_many({vpiNet}, obj_h, visited, top_nodes, [&](AstNode* port){
            if(port) {
              elaboratedInterface->addStmtp(port);
            }
          });
        }

        elaboratedInterface->name(objectName);
        std::string modType = vpi_get_str(vpiDefName, obj_h);
        sanitize_str(modType);
        if (objectName != modType) {
          AstPin *modPins = nullptr;
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

          AstPin *modParams = nullptr;
          itr = vpi_iterate(vpiParameter, obj_h);
          np = 0;
          while (vpiHandle vpi_child_obj = vpi_scan(itr) ) {
            std::string portName = vpi_get_str(vpiName, vpi_child_obj);
            sanitize_str(portName);

            AstParseRef *ref = new AstParseRef(new FileLine("uhdm"),
                                               AstParseRefExp::en::PX_TEXT,
                                               portName,
                                               nullptr,
                                               nullptr);
            AstPin *pin = new AstPin(new FileLine("uhdm"), ++np, portName, ref);
            if (!modParams)
                modParams = pin;
            else
                modParams->addNextNull(pin);

            vpi_free_object(vpi_child_obj);
          }
          vpi_free_object(itr);

          AstCell *cell = new AstCell(new FileLine("uhdm"), new FileLine("uhdm"),
              objectName, modType, modPins, modParams, nullptr);
          return cell;
        } else {
          // is top level
          return elaboratedInterface;
        }
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
      case vpiAlways: {
        VAlwaysKwd alwaysType;
        AstSenTree* senTree = nullptr;
        AstNode* body = nullptr;

        // Which always type is it?
        switch(vpi_get(vpiAlwaysType, obj_h)) {
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
              std::cout << "Unhandled always type" << std::endl;
              break;
            }
        }

        // Sensitivity list
        vpiHandle event_control_h = vpi_handle(vpiStmt, obj_h);
        if (event_control_h != nullptr) {
          AstNodeSenItem* senItemRoot;
          visit_one_to_one({vpiCondition}, event_control_h, visited, top_nodes,
            [&](AstNode* node){
              senItemRoot = reinterpret_cast<AstNodeSenItem*>(node);
            });
          senTree = new AstSenTree(new FileLine("uhdm"), senItemRoot);

          // Body of statements
          visit_one_to_one({vpiStmt}, event_control_h, visited, top_nodes,
            [&](AstNode* node){
              body = node;
            });
        }

        return new AstAlways(new FileLine("uhdm"), alwaysType, senTree, body);
      }
      case vpiBegin: {
        AstNode* body = nullptr;
        visit_one_to_many({vpiStmt}, obj_h, visited, top_nodes,
          [&](AstNode* node){
            if (body == nullptr) {
              body = node;
            } else {
              body->addNextNull(node);
            }
          });
        return new AstBegin(new FileLine("uhdm"), objectName, body);
      }
      case vpiIf:
      case vpiIfElse: {
        AstNode* condition;
        AstNode* statement;
        AstNode* elseStatement;

        visit_one_to_one({vpiCondition}, obj_h, visited, top_nodes,
          [&](AstNode* node){
            condition = node;
          });
        visit_one_to_one({vpiStmt}, obj_h, visited, top_nodes,
          [&](AstNode* node){
            statement = node;
          });
        if (objectType == vpiIfElse) {
          visit_one_to_one({vpiElseStmt}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              elseStatement = node;
            });
        }
        return new AstIf(new FileLine("uhdm"), condition, statement, elseStatement);
      }
      case vpiOperation: {
        AstNode* rhs = nullptr;
        AstNode* lhs = nullptr;
        auto operation = vpi_get(vpiOpType, obj_h);
        switch (operation) {
          case vpiNotOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              rhs = node;
            });
            return new AstNot(new FileLine("uhdm"), rhs);
          }
          case vpiBitAndOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (rhs == nullptr) {
                  rhs = node;
                } else {
                  lhs = node;
                }
              });
            return new AstAnd(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiBitOrOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (rhs == nullptr) {
                  rhs = node;
                } else {
                  lhs = node;
                }
              });
            return new AstOr(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiBitXorOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (rhs == nullptr) {
                  rhs = node;
                } else {
                  lhs = node;
                }
              });
            return new AstXor(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiBitXnorOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (rhs == nullptr) {
                  rhs = node;
                } else {
                  lhs = node;
                }
              });
            return new AstXnor(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiEventOrOp: {
            // Do not create a separate node
            // Chain operand nodes instead
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (rhs == nullptr) {
                  rhs = node;
                } else {
                  rhs->addNextNull(node);
                }
              });
            return rhs;
          }
          case vpiPosedgeOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              rhs = node;
            });
            return new AstSenItem(new FileLine("uhdm"),
                                  AstEdgeType::ET_POSEDGE,
                                  rhs);
          }
          case vpiNegedgeOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              rhs = node;
            });
            return new AstSenItem(new FileLine("uhdm"),
                                  AstEdgeType::ET_NEGEDGE,
                                  rhs);
          }
          default: {
            std::cout << "\t! Encountered unhandled operation" << std::endl;
            break;
          }
        }
        return nullptr;
      }
      case vpiConstant: {
        auto type = vpi_get(vpiConstType, obj_h);
        s_vpi_value val;
        vpi_get_value(obj_h, &val);
        switch (val.format) {
          case vpiIntVal: {
            return new AstConst(new FileLine("uhdm"), AstConst::Unsized32(), (val.value.integer));
          }
          default: {
            std::cout << "\t! Encountered unhandled constant type" << std::endl;
            break;
          }
        }
        return nullptr;
      }

      // What we can see (but don't support yet)
      case vpiClassObj:
      case vpiClassDefn:
      case vpiPackage:
        break; // Be silent
      default: {
        // Notify we have something unhandled
        std::cout << "Unhandled type: " << objectType << std::endl;
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
