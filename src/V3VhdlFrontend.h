#ifndef _V3VHDLPARSER_H_
#define _V3VHDLPARSER_H_
#include "V3Ast.h"
#include "V3AstNodes.h"
#include "V3Global.h"
#include "V3ParseSym.h"
#include <iostream>
#include <string>
#include <fstream>
#include <map>
#include <vector>
#include "rapidjson/include/rapidjson/document.h"
#include "rapidjson/include/rapidjson/istreamwrapper.h"

using namespace std;
using namespace rapidjson;

class V3VhdlFrontend {
public:
  V3VhdlFrontend(V3ParseSym *symtable);
  void parseFiles();
private:
  std::string exec(const char* cmd);
  AstNode* createSupplyExpr(FileLine* fileline, string name, int value);
  AstNodeDType* createArray(AstNodeDType* basep, AstNodeRange* nrangep, bool isPacked);
  AstVar* createVariable(FileLine* fileline, string name, AstNodeRange* arrayp, AstNode* attrsp);
  AstNodeDType *translateType(Value::ConstObject item);
  AstNode *translateObject(Value::ConstObject item);
  void translate(const char* filename);
  bool allTracingOn(FileLine* fl) {
    return v3Global.opt.trace() && fl->tracingOn();
  }

  unsigned long pinnum;
  map<string, AstNode*> m_entities;
  AstAlways *current_process;
  V3ParseSym *symt;
  VVarType        m_varDecl;
  VDirection  m_varIO;
  AstNodeDType* m_varDTypep;
};

#endif
