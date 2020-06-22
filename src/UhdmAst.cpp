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

  std::map<std::string, AstNode*> pinMap;
  std::set<std::tuple<std::string, int, int>> coverage_set;

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

    const unsigned int currentLine = vpi_get(vpiLineNo, obj_h);
    const unsigned int objectType = vpi_get(vpiType, obj_h);
    std::cout << "Object: " << objectName
              << " of type " << objectType
              << " @ " << currentLine
              << std::endl;
    if (file_name) {
      coverage_set.insert({file_name, currentLine, objectType});
    }

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
      case vpiPackage: {
        auto* package = new AstPackage(new FileLine("uhdm"), objectName);
        visit_one_to_many({
            //vpiParameter,  // use vpiParamAssign instead
            vpiParamAssign,
            vpiTypedef
            },
            obj_h,
            visited,
            top_nodes,
            [&](AstNode* item) {
              if (item != nullptr) {
                package->addStmtp(item);
              }
            });

        return package;
      }
      case vpiPort: {
        static unsigned numPorts;
        AstPort *port = nullptr;
        AstVar *var = nullptr;
        AstRange* rangeNode = nullptr;

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
            auto* dtype = new AstIfaceRefDType(new FileLine("uhdm"),
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
          // Get range from actual
          visit_one_to_many({vpiRange}, actual_h, visited, top_nodes,
              [&](AstNode* node){
                rangeNode = reinterpret_cast<AstRange*>(node);
              });
        }
        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                                  AstBasicDTypeKwd::LOGIC);
        dtype->rangep(rangeNode);
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
            var->varType(AstVarType::PORT);
            // Create and store another node to be retrieved in vpiNet visit
            // Done here because we do not have range information for ports in vpiNet
            auto* netDtype = new AstBasicDType(new FileLine("uhdm"),
                                               AstBasicDTypeKwd::LOGIC);
            auto* netVar = new AstVar(new FileLine("uhdm"),
                             AstVarType::VAR,
                             objectName,
                             netDtype);
            netVar->childDTypep(netDtype);
            pinMap[objectName] = netVar;
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
              vpiPort,
              vpiInterface,
              vpiModule,
              vpiContAssign,
              vpiNet,
              vpiVariables,
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
              vpiModule,
              vpiContAssign,
              vpiParamAssign,
              vpiProcess,
              vpiTaskFunc,
              vpiTypedef,
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
              objectName, modType, modPins, nullptr, nullptr);
          return cell;
        }
        break;
      }
      case vpiAssignment:
      case vpiAssignStmt:
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

        if (rvalue != nullptr && rvalue->type() == AstType::en::atFOpen) {
          // Not really an assignment, AstFOpen node takes care of the lhs
          return rvalue;
        }
        if (lvalue && rvalue) {
          if (objectType == vpiAssignment) {
            auto blocking = vpi_get(vpiBlocking, obj_h);
            if (blocking) {
              return new AstAssign(new FileLine("uhdm"), lvalue, rvalue);
            } else {
              return new AstAssignDly(new FileLine("uhdm"), lvalue, rvalue);
            }
          } else if (objectType == vpiContAssign || objectType == vpiAssignStmt)
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
        AstVarType net_type = AstVarType::UNKNOWN;
        AstBasicDTypeKwd dtypeKwd = AstBasicDTypeKwd::LOGIC_IMPLICIT;

        auto netType = vpi_get(vpiNetType, obj_h);

        auto pinIt = pinMap.find(objectName);
        if (pinIt != pinMap.end()) {
          return pinIt->second;
        }
        // If parent has port with this name: skip
        auto parent_h = vpi_handle(vpiParent, obj_h);
        if (parent_h) {
          vpiHandle itr = vpi_iterate(vpiPort, parent_h);
          while (vpiHandle port_h = vpi_scan(itr) ) {
            std::string childName = vpi_get_str(vpiName, port_h);
            sanitize_str(childName);
            if (objectName == childName) {
              if (const int n = vpi_get(vpiDirection, port_h)) {
                if (n == vpiOutput) {
                  auto it = pinMap.find(objectName);
                  if (it != pinMap.end()) {
                    return it->second;
                  }
                } else {
                  // Dummy node just to store something
                  // This won't be used
                  pinMap[objectName] = new AstFinal(new FileLine("uhdm"), nullptr);
                  return nullptr;
                }
              }
            }
            vpi_free_object(port_h);
          }
          vpi_free_object(itr);
          if (vpi_get(vpiType, parent_h) == vpiInterface) {
            netType = vpiReg;  // They are not specified otherwise in UHDM
          }
        }

        //Check if this was a port pin
        auto it = pinMap.find(objectName);
        if (it != pinMap.end()) {
          return nullptr;
        }

        switch (netType) {
          case vpiLogicNet:
          case vpiReg: {
            net_type = AstVarType::VAR;
            dtypeKwd = AstBasicDTypeKwd::LOGIC;
            break;
          }
          case vpiWire: {
            net_type = AstVarType::WIRE;
            dtypeKwd = AstBasicDTypeKwd::LOGIC;
            break;
          }
          default: {
            v3error("\t! Unhandled net type: " << netType);
            break;
          }
        }
        if (net_type == AstVarType::UNKNOWN) {
          // Not set in case above, most likely a "false" port net
          return nullptr; // Skip this net
        }
        AstRange* rangeNode = nullptr;
        visit_one_to_many({vpiRange}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              rangeNode = reinterpret_cast<AstRange*>(node);
            });

        dtype = new AstBasicDType(new FileLine("uhdm"), dtypeKwd);
        dtype->rangep(rangeNode);
        auto *v = new AstVar(new FileLine("uhdm"), net_type, objectName, dtype);
        v->childDTypep(dtype);
        return v;
      }
      case vpiStructVar: {
        // Typespec is visited separately, grab only reference here
        auto typespec_h = vpi_handle(vpiTypespec, obj_h);
        std::string data_type_name = vpi_get_str(vpiName, typespec_h);
        auto* dtype = new AstRefDType(new FileLine("uhdm"), data_type_name);

        auto* v = new AstVar(new FileLine("uhdm"),
                             AstVarType::VAR,
                             objectName,
                             dtype);
        v->childDTypep(dtype);
        return v;
      }
      case vpiParamAssign: {
        AstVar* parameter = nullptr;
        AstNode* parameter_value = nullptr;
        visit_one_to_one({vpiLhs}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              parameter = reinterpret_cast<AstVar*>(node);
            });
        visit_one_to_one({vpiRhs}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              parameter_value = node;
            });

        parameter->valuep(parameter_value);

        return parameter;
      }
      case vpiParameter: {
        AstNode* msbNode = nullptr;
        AstNode* lsbNode = nullptr;
        AstRange* rangeNode = nullptr;
        auto leftRange_h  = vpi_handle(vpiLeftRange, obj_h);
        if (leftRange_h) {
          msbNode = visit_object(leftRange_h, visited, top_nodes);
        }
        auto rightRange_h  = vpi_handle(vpiRightRange, obj_h);
        if (rightRange_h) {
          lsbNode = visit_object(rightRange_h, visited, top_nodes);
        }
        if (msbNode && lsbNode) {
          rangeNode = new AstRange(new FileLine("uhdm"), msbNode, lsbNode);
        }

        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                                        AstBasicDTypeKwd::LOGIC_IMPLICIT);
        dtype->rangep(rangeNode);
        auto* parameter = new AstVar(new FileLine("uhdm"),
                               AstVarType::GPARAM,
                               objectName,
                               dtype);
        parameter->childDTypep(dtype);
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

          AstCell *cell = new AstCell(new FileLine("uhdm"), new FileLine("uhdm"),
              objectName, modType, modPins, nullptr, nullptr);
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
        while (vpiHandle io_h = vpi_scan(io_itr) ) {
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
            modport_vars->addNext(io_node);
          else
            modport_vars = io_node;
          vpi_free_object(io_h);
        }
        vpi_free_object(io_itr);

        return new AstModport(new FileLine("uhdm"), objectName, modport_vars);
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
        AstRange* var_range = nullptr;
        visit_one_to_many({vpiRange}, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
                var_range = reinterpret_cast<AstRange*>(item);
            }
          });
        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                              AstBasicDTypeKwd::LOGIC);
        dtype->rangep(var_range);
        auto* var = new AstVar(new FileLine("uhdm"),
                         AstVarType::PORT,
                         objectName,
                         dtype);
        var->childDTypep(dtype);
        var->declDirection(dir);
        var->direction(dir);
        return var;
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
              v3error("Unhandled always type");
              break;
            }
        }

        if (alwaysType != VAlwaysKwd::ALWAYS_COMB
            && alwaysType != VAlwaysKwd::ALWAYS_LATCH) {
          // Sensitivity list
          vpiHandle event_control_h = vpi_handle(vpiStmt, obj_h);
          if (event_control_h != nullptr) {
            AstNodeSenItem* senItemRoot;
            visit_one_to_one({vpiCondition}, event_control_h, visited, top_nodes,
              [&](AstNode* node){
                if (node->type() == AstType::en::atSenItem) {
                  senItemRoot = reinterpret_cast<AstNodeSenItem*>(node);
                  }
                else { // wrap this in a AstSenItem
                  senItemRoot = new AstSenItem(new FileLine("uhdm"),
                                               AstEdgeType::ET_ANYEDGE,
                                               node);
                  }
              });
            senTree = new AstSenTree(new FileLine("uhdm"), senItemRoot);

            // Body of statements
            visit_one_to_one({vpiStmt}, event_control_h, visited, top_nodes,
              [&](AstNode* node){
                body = node;
              });
          }
        } else {
          // Body of statements
          visit_one_to_one({vpiStmt}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              body = node;
            });
        }

        return new AstAlways(new FileLine("uhdm"), alwaysType, senTree, body);
      }
      case vpiInitial: {
        AstNode* body = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, visited, top_nodes,
          [&](AstNode* node){
            body = node;
          });
        return new AstInitial(new FileLine("uhdm"), body);
      }
      case vpiFinal: {
        AstNode* body = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, visited, top_nodes,
          [&](AstNode* node){
            body = node;
          });
        return new AstFinal(new FileLine("uhdm"), body);
      }
      case vpiNamedBegin:
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
        if (objectType == vpiBegin) {
          objectName = "";  // avoid storing parent name
        }
        return new AstBegin(new FileLine("uhdm"), objectName, body);
      }
      case vpiIf:
      case vpiIfElse: {
        AstNode* condition = nullptr;
        AstNode* statement = nullptr;
        AstNode* elseStatement = nullptr;

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
        visit_one_to_one({vpiCondition}, obj_h, visited, top_nodes,
          [&](AstNode* node){
            conditionNode = node;
          });
        AstNode* itemNodes = nullptr;
        visit_one_to_many({vpiCaseItem}, obj_h, visited, top_nodes,
            [&](AstNode* item){
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
        visit_one_to_many({vpiExpr}, obj_h, visited, top_nodes,
            [&](AstNode* item){
              if (item) {
                if (expressionNode == nullptr) {
                  expressionNode = item;
                } else {
                  expressionNode->addNextNull(item);
                }
              }
            });
        AstNode* bodyNode = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, visited, top_nodes,
          [&](AstNode* node){
            bodyNode = node;
          });
        return new AstCaseItem(new FileLine("uhdm"), expressionNode, bodyNode);
      }
      case vpiOperation: {
        AstNode* rhs = nullptr;
        AstNode* lhs = nullptr;
        auto operation = vpi_get(vpiOpType, obj_h);
        switch (operation) {
          case vpiBitNegOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              rhs = node;
            });
            return new AstNot(new FileLine("uhdm"), rhs);
          }
          case vpiNotOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              lhs = node;
            });
            return new AstLogNot(new FileLine("uhdm"), lhs);
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
          case vpiUnaryOrOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (rhs == nullptr) {
                  rhs = node;
                }
              });
            return new AstRedOr(new FileLine("uhdm"), rhs);
          }
          case vpiEventOrOp: {
            // Do not create a separate node
            // Chain operand nodes instead
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
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
                    auto* wrapper = new AstSenItem(new FileLine("uhdm"),
                                                   AstEdgeType::ET_ANYEDGE,
                                                   node);
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
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstLogAnd(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiLogOrOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstLogOr(new FileLine("uhdm"), lhs, rhs);
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
          case vpiEqOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstEq(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiNeqOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstNeq(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiGtOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstGt(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiGeOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstGte(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiLtOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstLt(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiLeOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstLte(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiPlusOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstAdd(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiSubOp:
          case vpiMinusOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstSub(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiAddOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstAdd(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiConditionOp: {
            AstNode* condition = nullptr;
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
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
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if(node != nullptr) {
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
            }
            rhs = new AstConst(new FileLine("uhdm"), 1);
            return new AstReplicate(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiMultiConcatOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
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
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstShiftL(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiRShiftOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstShiftR(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiArithRShiftOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstShiftRS(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiInsideOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
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
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                }
              });
            visit_one_to_one({vpiTypespec}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (rhs == nullptr) {
                  rhs = node;
                }
              });
            return new AstCastParse(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiPowerOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
                if (lhs == nullptr) {
                  lhs = node;
                } else {
                  rhs = node;
                }
              });
            return new AstPow(new FileLine("uhdm"), lhs, rhs);
          }
          case vpiAssignmentPatternOp: {
            visit_one_to_many({vpiOperand}, obj_h, visited, top_nodes,
              [&](AstNode* node){
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
      case vpiIntegerTypespec: // Handling determined by type returned from vpi_value
      case vpiEnumConst:
      case vpiConstant: {
        s_vpi_value val;
        vpi_get_value(obj_h, &val);
        AstConst* constNode = nullptr;
        switch (val.format) {
          case vpiScalarVal: {
            std::string valStr = std::to_string(val.value.scalar);
            V3Number value(constNode, valStr.c_str());
            constNode = new AstConst(new FileLine("uhdm"), value);
            return constNode;
          }
          case vpiIntVal: {
            std::string valStr = std::to_string(val.value.integer);
            if (valStr[0] == '-') {
              valStr = valStr.substr(1);
              V3Number value(constNode, valStr.c_str());
              constNode = new AstConst(new FileLine("uhdm"), value);
              return new AstNegate(new FileLine("uhdm"), constNode);
            }
            V3Number value(constNode, valStr.c_str());
            constNode = new AstConst(new FileLine("uhdm"), value);
            return constNode;
          }
          case vpiRealVal: {
            std::string valStr = std::to_string(val.value.real);
            V3Number value(constNode, valStr.c_str());
            constNode = new AstConst(new FileLine("uhdm"), value);
            return constNode;
          }
          case vpiBinStrVal:
          case vpiOctStrVal:
          case vpiDecStrVal:
          case vpiHexStrVal: {
            std::string valStr(val.value.str);
            V3Number value(constNode, valStr.c_str());
            constNode = new AstConst(new FileLine("uhdm"), value);
            return constNode;
          }
          case vpiStringVal: {
            std::string valStr(val.value.str);
            constNode = new AstConst(new FileLine("uhdm"), AstConst::VerilogStringLiteral(), valStr);
            return constNode;
          }
          default: {
            v3error("\t! Encountered unhandled constant type " << val.format);
            break;
          }
        }
        return nullptr;
      }
      case vpiBitSelect: {
        auto* fromp = new AstParseRef(new FileLine("uhdm"),
                                               AstParseRefExp::en::PX_TEXT,
                                               objectName,
                                               nullptr,
                                               nullptr);
        auto bitHandle = vpi_handle({vpiIndex}, obj_h);
        AstNode* bitp = nullptr;
        visit_one_to_one({vpiIndex}, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
              bitp = item;
            }
          });
        return new AstSelBit(new FileLine("uhdm"), fromp, bitp);
      }
      case vpiTask: {
        AstNode* statements = nullptr;
        visit_one_to_one({vpiStmt}, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
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
          visit_one_to_many({vpiRange}, return_h, visited, top_nodes,
            [&](AstNode* item){
              if (item) {
                  returnRange = reinterpret_cast<AstRange*>(item);
              }
            });
        }
        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                                  AstBasicDTypeKwd::LOGIC);
        dtype->rangep(returnRange);
        function_vars = dtype;

        visit_one_to_many({vpiIODecl}, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
              if (statements)
                statements->addNextNull(item);
              else
                statements = item;
            }
          });

        visit_one_to_one({vpiStmt}, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
              statements->addNextNull(item);
            }
          });
        return new AstFunc(new FileLine("uhdm"), objectName, statements, function_vars);
      }
      case vpiReturn:
      case vpiReturnStmt: {
        AstNode* condition = nullptr;
        visit_one_to_one({vpiCondition}, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
              condition = item;
            }
          });
        return new AstReturn(new FileLine("uhdm"), condition);
        }
      case vpiFuncCall: {
        AstNode* arguments = nullptr;
        visit_one_to_many({vpiArgument}, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
                if (arguments == nullptr) {
                  arguments = new AstArg(new FileLine("uhdm"), "", item);
                } else {
                  arguments->addNextNull(new AstArg(new FileLine("uhdm"), "", item));
                }
            }
          });
        AstFuncRef* func_call = new AstFuncRef(new FileLine("uhdm"), objectName, arguments);
        return func_call;
      }
      case vpiSysFuncCall: {
        std::vector<AstNode*> arguments;
        visit_one_to_many({vpiArgument}, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
              arguments.push_back(item);
            }
          });

        if (objectName == "$signed") {
          return new AstSigned(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$unsigned") {
          return new AstUnsigned(new FileLine("uhdm"), arguments[0]);
        } else if (objectName == "$time") {
          return new AstTime(new FileLine("uhdm"));
        } else if (objectName == "$display") {
          return new AstDisplay(new FileLine("uhdm"),
                                AstDisplayType(),
                                nullptr,
                                arguments[0]);
        } else if (objectName == "$value$plusargs") {
          return new AstValuePlusArgs(new FileLine("uhdm"),
                                      arguments[0],
                                      arguments[1]);
        } else if (objectName == "$sformat") {
          // TODO: This asssumes a string constant, but it could be a fairly
          // complex structure instead
          auto s = reinterpret_cast<AstConst*>(arguments[1])->num().toString();
          return new AstSFormat(new FileLine("uhdm"),
                                arguments[0],
                                s,
                                arguments[2]);
        } else if (objectName == "$sformatf") {
          auto s = reinterpret_cast<AstConst*>(arguments[0])->num().toString();
          return new AstSFormatF(new FileLine("uhdm"),
                                 s,
                                 false,
                                 arguments[1]);
        } else if (objectName == "$fopen") {
          // We need to obtain the variable in which the descriptor will be stored
          // This usually will be LHS of an assignment fd = $fopen(...)
          auto parent_h = vpi_handle({vpiParent}, obj_h);
          auto lhs_h = vpi_handle({vpiLhs}, parent_h);
          AstNode* fd = nullptr;
          if (lhs_h) {
            fd = visit_object(lhs_h, visited, top_nodes);
          }
          return new AstFOpen(new FileLine("uhdm"),
                              fd,
                              arguments[0],
                              arguments[1]);
        } else if (objectName == "$fwrite") {
          return new AstDisplay(new FileLine("uhdm"),
                                AstDisplayType(AstDisplayType::en::DT_WRITE),
                                arguments[0],
                                arguments[1]);
        } else {
            v3error("\t! Encountered unhandled SysFuncCall: " << objectName);
        }
        // Should not be reached
        return nullptr;
      }
      case vpiRange: {
        AstNode* msbNode = nullptr;
        AstNode* lsbNode = nullptr;
        AstRange* rangeNode = nullptr;
        auto leftRange_h  = vpi_handle(vpiLeftRange, obj_h);
        if (leftRange_h) {
          msbNode = visit_object(leftRange_h, visited, top_nodes);
        }
        auto rightRange_h  = vpi_handle(vpiRightRange, obj_h);
        if (rightRange_h) {
          lsbNode = visit_object(rightRange_h, visited, top_nodes);
        }
        if (msbNode && lsbNode) {
          rangeNode = new AstRange(new FileLine("uhdm"), msbNode, lsbNode);
        }
        return rangeNode;
      }
      case vpiPartSelect: {
        AstNode* msbNode = nullptr;
        AstNode* lsbNode = nullptr;
        AstNode* fromNode = nullptr;

        visit_one_to_one({
            vpiLeftRange,
            vpiRightRange,
            vpiParent,
            }, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
              if (msbNode == nullptr) {
                msbNode = item;
              } else if (lsbNode == nullptr) {
                lsbNode = item;
              } else if (fromNode == nullptr) {
                fromNode = item;
              }
            }
          });
        return new AstSelExtract(new FileLine("uhdm"), fromNode, msbNode, lsbNode);
      }
      case vpiIndexedPartSelect: {
        AstNode* bit = nullptr;
        AstNode* width = nullptr;
        AstNode* fromNode = nullptr;

        visit_one_to_one({
            vpiBaseExpr,
            vpiWidthExpr,
            vpiParent,
            }, obj_h, visited, top_nodes,
          [&](AstNode* item){
            if (item) {
              if (bit == nullptr) {
                bit = item;
              } else if (width == nullptr) {
                width = item;
              } else if (fromNode == nullptr) {
                fromNode = item;
              }
            }
          });

        auto type = vpi_get(vpiIndexedPartSelectType, obj_h);
        if (type == vpiPosIndexed) {
          return new AstSelPlus(new FileLine("uhdm"), fromNode, bit, width);
        } else if (type == vpiNegIndexed) {
          return new AstSelMinus(new FileLine("uhdm"), fromNode, bit, width);
        } else {
          return nullptr;
        }
      }

      case vpiBitTypespec: {
        AstRange* rangeNode = nullptr;
        visit_one_to_many({vpiRange}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              rangeNode = reinterpret_cast<AstRange*>(node);
            });
        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                                        AstBasicDTypeKwd::BIT);
        dtype->rangep(rangeNode);
        return dtype;
      }
      case vpiLogicTypespec: {
        AstRange* rangeNode = nullptr;
        visit_one_to_many({vpiRange}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              rangeNode = reinterpret_cast<AstRange*>(node);
            });
        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                                  AstBasicDTypeKwd::LOGIC);
        dtype->rangep(rangeNode);
        return dtype;
      }
      case vpiIntTypespec: {
        AstRange* rangeNode = nullptr;
        visit_one_to_many({vpiRange}, obj_h, visited, top_nodes,
            [&](AstNode* node){
              rangeNode = reinterpret_cast<AstRange*>(node);
            });
        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                                        AstBasicDTypeKwd::INT);
        dtype->rangep(rangeNode);
        return dtype;
      }
      case vpiVoidTypespec: {
        return new AstRefDType(new FileLine("uhdm"), objectName);
      }
      case vpiEnumTypespec: {
        AstNode* enum_members = nullptr;
        AstNodeDType* enum_member_dtype = nullptr;
        visit_one_to_many({
            vpiEnumConst
            },
            obj_h,
            visited,
            top_nodes,
            [&](AstNode* item) {
              if (item != nullptr) {
                auto* wrapped_item = new AstEnumItem(new FileLine("uhdm"),
                                                     item->name(),
                                                     nullptr,
                                                     item);
                if (enum_members == nullptr) {
                  enum_members = wrapped_item;
                } else {
                  enum_members->addNextNull(wrapped_item);
                }
              }
            });
        visit_one_to_one({
            vpiBaseTypespec
            },
            obj_h,
            visited,
            top_nodes,
            [&](AstNode* item) {
              if (item != nullptr) {
                enum_member_dtype = reinterpret_cast<AstNodeDType*>(item);
              }
            });
        if (enum_member_dtype == nullptr) {
          // No data type specified, use default
          enum_member_dtype = new AstBasicDType(new FileLine("uhdm"),
                                                AstBasicDTypeKwd::INT);
        }
        auto* enum_dtype = new AstEnumDType(new FileLine("uhdm"),
                                            VFlagChildDType(),
                                            enum_member_dtype,
                                            enum_members);
        auto* dtype = new AstDefImplicitDType(new FileLine("uhdm"),
                                              objectName,
                                              nullptr,
                                              VFlagChildDType(),
                                              enum_dtype);
        auto* enum_type = new AstTypedef(new FileLine("uhdm"),
                                         objectName,
                                         nullptr,
                                         VFlagChildDType(),
                                         dtype);
        return enum_type;
      }
      case vpiStructTypespec: {
        auto* struct_dtype = new AstStructDType(new FileLine("uhdm"),
                                                AstNumeric());
        visit_one_to_many({vpiTypespecMember}, obj_h, visited, top_nodes,
            [&](AstNode* item) {
              if (item != nullptr) {
                struct_dtype->addMembersp(item);
              }
            });
        auto* dtype = new AstDefImplicitDType(new FileLine("uhdm"),
                                              objectName,
                                              nullptr,
                                              VFlagChildDType(),
                                              struct_dtype);
        auto* struct_type = new AstTypedef(new FileLine("uhdm"),
                                           objectName,
                                           nullptr,
                                           VFlagChildDType(),
                                           dtype);
        return struct_type;
      }
      case vpiTypespecMember: {
        AstNodeDType* typespec = nullptr;
        visit_one_to_one({vpiTypespec}, obj_h, visited, top_nodes,
            [&](AstNode* item) {
              if (item != nullptr) {
                typespec = reinterpret_cast<AstNodeDType*>(item);
              }
            });
        if (typespec != nullptr) {
          auto * member =  new AstMemberDType(new FileLine("uhdm"),
              objectName,
              reinterpret_cast<AstNodeDType*>(typespec));
          member->childDTypep(typespec);
          return member;
        }
      }
      case vpiLogicVar: {
        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                                  AstBasicDTypeKwd::LOGIC);
        auto* var = new AstVar(new FileLine("uhdm"),
                         AstVarType::VAR,
                         objectName,
                         dtype);
        return var;
      }
      case vpiEnumVar: {
        auto* dtype = new AstBasicDType(new FileLine("uhdm"),
                                  AstBasicDTypeKwd::INTEGER);
        auto* var = new AstVar(new FileLine("uhdm"),
                         AstVarType::VAR,
                         objectName,
                         dtype);
        return var;
      }

      // What we can see (but don't support yet)
      case vpiClassObj:
      case vpiClassDefn:
        break; // Be silent
      case vpiUnsupportedStmt:
        v3info("\t! This statement is unsupported in UHDM: "
               << file_name << ":" << currentLine);
        // Dummy statement to keep parsing
        return new AstTime(new FileLine("uhdm"));
        break;
      case vpiUnsupportedExpr:
        v3info("\t! This expression is unsupported in UHDM: "
               << file_name << ":" << currentLine);
        // Dummy expression to keep parsing
        return new AstConst(new FileLine("uhdm"), 1);
        break;
      default: {
        // Notify we have something unhandled
        v3error("\t! Unhandled type: " << objectType);
        break;
      }
    }

    return nullptr;
  }

  std::vector<AstNodeModule*> visit_designs (const std::vector<vpiHandle>& designs,
                                             std::ostream& coverage_report_stream) {
    std::set<const UHDM::BaseClass*> visited;
    std::map<std::string, AstNodeModule*> top_nodes;
    for (auto design : designs) {
        visit_one_to_many({
            UHDM::uhdmallInterfaces,
            UHDM::uhdmallModules,
            UHDM::uhdmallPackages,
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
              for (auto entry : coverage_set) {
                coverage_report_stream << std::get<0>(entry)
                                << ":" << std::get<1>(entry)
                                << ":" << std::get<2>(entry) << std::endl;
              }
              coverage_set.clear();
            });
    }
    std::vector<AstNodeModule*> nodes;
    for (auto node : top_nodes)
              nodes.push_back(node.second);
    return nodes;
  }

}
