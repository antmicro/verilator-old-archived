#include "V3VhdlFrontend.h"
#include "V3Global.h"
#include <iostream>
#include <sstream>
#include <cstdio>
#include <stdexcept>
#include <stdio.h>
#include <string>
#include "V3Global.h"
#include "V3Ast.h"
#include "V3FileLine.h"

#define VARIO(type) { m_varIO = VDirection::type; }
#define VARDECL(type) { m_varDecl = VVarType::type; }
#define VARDTYPE(dtypep) { m_varDTypep = dtypep; }
#define VARRESET() { VARDECL(UNKNOWN); VARIO(NONE); VARDTYPE(NULL); }

using namespace std;


V3VhdlFrontend::V3VhdlFrontend(V3ParseSym *symtable) : symt(symtable) {}

std::string V3VhdlFrontend::exec(const char* cmd) {
    char buffer[128];
    std::string result = "";
    FILE* pipe = popen(cmd, "r");
    if (!pipe) throw std::runtime_error("popen() failed!");
    try {
        while (fgets(buffer, sizeof buffer, pipe) != NULL) {
            result += buffer;
        }
    } catch (...) {
        pclose(pipe);
        throw;
    }
    pclose(pipe);
    return result;
}

void V3VhdlFrontend::parseFiles() {
  const V3StringList& vhdFiles = v3Global.opt.vhdFiles();
  if (!vhdFiles.size())
    return;
  std::string command = "python3 vhdl_convert.py";
  for (auto s : vhdFiles)
    command += " " + s;
  std::string out = exec(command.c_str());
  cout << out << endl;
  translate(out.c_str());
}

AstNode* V3VhdlFrontend::createSupplyExpr(FileLine* fileline, string name, int value) {
    return new AstAssignW(fileline, new AstVarRef(fileline, name, VAccess()),
                          new AstConst(fileline, AstConst::StringToParse(),
				       (value ? "'1" : "'0")));
}

AstNodeDType* V3VhdlFrontend::createArray(AstNodeDType* basep, AstNodeRange* nrangep, bool isPacked) {
    AstNodeDType* arrayp = basep;
    if (nrangep) {
        while (nrangep->nextp()) nrangep = VN_CAST(nrangep->nextp(), NodeRange);
        while (nrangep) {
            AstNodeRange* prevp = VN_CAST(nrangep->backp(), NodeRange);
            if (prevp) nrangep->unlinkFrBack();
            AstRange* rangep = VN_CAST(nrangep, Range);
            if (!rangep) {
                if (!VN_IS(nrangep, UnsizedRange)) nrangep->v3fatalSrc("Expected range or unsized range");
                arrayp = new AstUnsizedArrayDType(nrangep->fileline(), VFlagChildDType(), arrayp);
            } else if (isPacked) {
                arrayp = new AstPackArrayDType(rangep->fileline(), VFlagChildDType(), arrayp, rangep);
            } else {
                arrayp = new AstUnpackArrayDType(rangep->fileline(), VFlagChildDType(), arrayp, rangep);
            }
            nrangep = prevp;
        }
    }
    return arrayp;
}

AstVar* V3VhdlFrontend::createVariable(FileLine* fileline, string name, AstNodeRange* arrayp, AstNode* attrsp) {
    AstNodeDType* dtypep = m_varDTypep;
    if (m_varIO == VDirection::NONE
	&& m_varDecl == VVarType::PORT) {
	if (dtypep) fileline->v3error("Unsupported: Ranges ignored in port-lists");
	return NULL;
    }
    if (m_varDecl == VVarType::WREAL) {
	dtypep = new AstBasicDType(fileline,VBasicDTypeKwd::DOUBLE);
    }
    if (!dtypep) {
	dtypep = new AstBasicDType(fileline, VBasicDTypeKwd::LOGIC_IMPLICIT);
    } else {
	dtypep = dtypep->cloneTree(false);
    }
    VVarType type = m_varDecl;
    if (type == VVarType::UNKNOWN) {
        if (m_varIO.isAny()) {
            type = VVarType::PORT;
        } else {
            fileline->v3fatalSrc("Unknown signal type declared");
        }
    }
    if (type == VVarType::GENVAR) {
	if (arrayp) fileline->v3error("Genvars may not be arrayed: "<<name);
    }

    AstNodeDType* arrayDTypep = createArray(dtypep, arrayp, false);

    AstVar* nodep = new AstVar(fileline, type, name, VFlagChildDType(), arrayDTypep);
    nodep->addAttrsp(attrsp);
    if (m_varDecl != VVarType::UNKNOWN) nodep->combineType(m_varDecl);
    if (m_varIO != VDirection::NONE) {
        nodep->declDirection(m_varIO);
        nodep->direction(m_varIO);
    }

    if (m_varDecl == VVarType::SUPPLY0) {
	nodep->addNext(createSupplyExpr(fileline, nodep->name(), 0));
    }
    if (m_varDecl == VVarType::SUPPLY1) {
	nodep->addNext(createSupplyExpr(fileline, nodep->name(), 1));
    }
    if (VN_IS(dtypep, ParseTypeDType)) {
	AstNode* newp = new AstTypedefFwd(fileline, name);
	nodep->addNext(newp);
	symt->reinsert(newp);
    }
    if (nodep->isGenVar()) nodep->trace(false);
    else if (nodep->isParam() && !v3Global.opt.traceParams()) nodep->trace(false);
    else nodep->trace(allTracingOn(nodep->fileline()));

    return nodep;
}

AstNodeDType *V3VhdlFrontend::translateType(Value::ConstObject item) {
    FileLine *fl2 = new FileLine("");
    if (item["type"].IsString()) {
        if (std::string(item["type"].GetString()) == "std_logic") {
            return new AstBasicDType(fl2, VBasicDTypeKwd::LOGIC_IMPLICIT);
        } else if (std::string(item["type"].GetString()) == "integer") {
            return new AstBasicDType(fl2, VBasicDTypeKwd::INTEGER);
        } else {
            v3error("Failed to translate type " + std::string(item["type"].GetString()));
            return nullptr;
        }
    }
    return nullptr;
}

AstNode *V3VhdlFrontend::translateObject(Value::ConstObject item) {
    //printconstobject(item);
    auto obj = item;
    if (obj["__class__"] != "") {
        cout << obj["__class__"].GetString() << endl;
    }
    if (obj["__class__"] == "HdlModuleDec") {
        string module_name = obj["name"]["val"].GetString();
        AstModule *mod = new AstModule(new FileLine(""), module_name);
        symt->pushNew(mod);
        pinnum = 1;
        auto port_array = obj["ports"].GetArray();
        for(Value::ConstValueIterator m = port_array.Begin(); m != port_array.End(); ++m) {
            auto port_obj = m->GetObject();
            string direction = port_obj["direction"].GetString();
            if (direction == "IN") {
                VARIO(INPUT);
            } else if (direction == "OUT") {
                VARIO(OUTPUT);
            } else if (direction == "INOUT") {
                VARIO(INOUT);
            }
            VARDECL(PORT);
            AstPort *port = new AstPort(new FileLine(""), pinnum++, port_obj["name"]["val"].GetString());

            VARDTYPE(translateType(port_obj));
            mod->addStmtp(port);
            AstVar *port_var = createVariable(new FileLine(""), port->name(), NULL, NULL);
            symt->reinsert(port_var);
            mod->addStmtp(port_var);
        }
        pinnum = 0;

        v3Global.rootp()->addModulep(mod);
        symt->popScope(mod);
    } else if (obj["__class__"] == "HdlModuleDef") {
        AstModule *entity_mod = (AstModule*)symt->findEntUpward(obj["module_name"].GetString());
        symt->pushNew(entity_mod);
        if(entity_mod != NULL) {
            Value::ConstArray decls = obj["objs"].GetArray();

            for (Value::ConstValueIterator m = decls.Begin(); m != decls.End(); ++m) {
                AstNode * res = translateObject(m->GetObject());
                if(res) ((AstModule*)(entity_mod))->addStmtp(res);
            }
            symt->popScope(entity_mod);
        }

    } else if (obj["__class__"] == "HdlIdDef") {
        VARRESET();
        VARDECL(VAR);
        VARDTYPE(translateType(obj));
        string varName = obj["name"]["val"].GetString();
        AstVar *var = createVariable(new FileLine(""), varName, NULL, NULL);
        symt->reinsert(var);
        if (obj.HasMember("value"))
            var->valuep(new AstConst(new FileLine(""), obj["value"].GetInt()));
        return var;
    } else if (obj["__class__"] == "HdlCompInst") {
        static long instanceCount = 0;
        string inst_base = obj["module_name"]["ops"][1].GetString();
        AstCell * instance = new AstCell(new FileLine(""), new FileLine(""), obj["name"].GetString(), inst_base, NULL, NULL, NULL);
        Value::ConstArray ports = obj["port_map"].GetArray();
        long pinNum = 1;
        for(Value::ConstValueIterator m = ports.Begin(); m != ports.End(); ++m) {
            Value::ConstObject port = m->GetObject();
            instance->addPinsp(new AstPin(new FileLine(""), pinNum++, std::string(port["ops"][1].GetString()), new AstVarRef(new FileLine(""), std::string(port["ops"][0].GetString()), VAccess())));
        }
        return instance;
    } else if (obj["__class__"] == "HdlLibrary") {
    } else if (obj["__class__"] == "HdlImport") {
    } else {
        v3error("Unhandled type: " + std::string(obj["__class__"].GetString()));
    }
    return NULL;
}

void V3VhdlFrontend::translate(const char* json)
{
    Document document;
    document.Parse(json);
    for (Value::ConstValueIterator m = document.Begin(); m != document.End(); ++m) {
        Value::ConstObject obj = m->GetObject();
        translateObject(obj);
    }
}
