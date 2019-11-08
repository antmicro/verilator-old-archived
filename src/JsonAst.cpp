#include "V3Ast.h"
#include "json.hpp" // nlohmann

#if 0
# define debug(x) x
#else
# define debug(x) do { } while (0)
#endif

extern void * parseAstTree(nlohmann::json& json)
{
    std::string type = json.find("type").value();

    static unsigned np = 0;

    debug(std::cout << "Parsing: " << type << std::endl);
    auto _name = json.find("name");
    if (_name != json.end())
        debug(std::cout << "Name: " << _name.value() << std::endl);

    if (type == "AST_TOP") {
        std::vector<AstModule *> *modules = new std::vector<AstModule *>();

        auto nodes = json.find("nodes");
        for (auto itr = nodes->begin() ; itr != nodes->end() ; ++itr) {
            AstModule *module = reinterpret_cast<AstModule *>(parseAstTree(itr.value()));
            modules->push_back(module);
        }

        return modules;
    } else if (type == "AST_CELL") {
        auto name = json.find("name").value();
        debug(std::cout << "CELL name: " << name << std::endl);

        std::string modType;
        AstPin *modPins = nullptr;

        auto nodes = json.find("nodes");
        for (auto itr = nodes->begin() ; itr != nodes->end() ; ++itr) {
            auto type = itr->find("type").value();

            if (type == "AST_CELLTYPE") {
                modType = itr->find("name").value();
        } else if (type == "AST_ARGUMENT") {
            auto name  = itr->find("name").value();
            debug(std::cout << "AST_CELL: AST_ARGUMENT: " << name << std::endl);

            auto nodes = itr->find("nodes");
            if (nodes != itr->end()) {
                assert(nodes->size() == 1);

                AstParseRef *ref = reinterpret_cast<AstParseRef *>(parseAstTree(nodes.value()[0]));
                AstPin *pin = new AstPin(new FileLine("json"), ++np, name, ref);
                if (!modPins)
                    modPins = pin;
                else
                    modPins->addNextNull(pin);
            }
        } else
            debug(std::cout << "AST_CELL: Unknown type " << type << std::endl);
        }

        AstCell *cell = new AstCell(new FileLine("json"), new FileLine("json"),
            name, modType, modPins, nullptr, nullptr);

        return cell;
    } else if (type == "AST_MODULE") {
        auto name = json.find("name").value();

        AstModule *module = new AstModule(new FileLine("json"), name);

        auto nodes = json.find("nodes");
        for (auto itr = nodes->begin() ; itr != nodes->end() ; ++itr) {
            auto *node = reinterpret_cast<AstNode *>(parseAstTree(itr.value()));
            if (node)
                module->addStmtp(node);
        }

        return module;
    } else if (type == "AST_RANGE") {
        auto nodes = json.find("nodes").value();
        assert( (nodes.size() == 1) || (nodes.size() == 2) );

        if (nodes.size() == 1) {
            auto *ref0 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
            return new AstRange(new FileLine("json"), ref0, ref0);
        } else {
            auto *ref0 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
            auto *ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
            return new AstRange(new FileLine("json"), ref0, ref1);
        }
    } else if (type == "AST_PARAMETER") {
        auto name = json.find("name").value();
        debug(std::cout << "AST_PARAMETER: Name: " << name << std::endl);

        auto nodes = json.find("nodes").value();
        assert( (nodes.size() == 1) || (nodes.size() == 2) );

        AstConst *value = nullptr;
        if (nodes.size() >= 1) {
            auto type = nodes[0].find("type").value();
            assert(type == "AST_CONSTANT");
            value = reinterpret_cast<AstConst *>(parseAstTree(nodes[0]));
        }

        AstRange *range = nullptr;
        if (nodes.size() >= 2) {
            auto type = nodes[1].find("type").value();
            assert(type == "AST_RANGE");
            range = reinterpret_cast<AstRange *>(parseAstTree(nodes[1]));
        }

        AstBasicDType *dtype = nullptr;
        if (range) {
            dtype = new AstBasicDType(new FileLine("json"), VFlagLogicPacked(), range->elementsConst());
            dtype->rangep(range);
        } else
            dtype = new AstBasicDType(new FileLine("json"), AstBasicDTypeKwd::LOGIC_IMPLICIT);

        // FIXME: AstVarType
        AstVar *param = new AstVar(new FileLine("json"), AstVarType::GPARAM, name, dtype);
        param->childDTypep(dtype);

        AstConst *cnst = new AstConst(new FileLine("json"), AstConst::WidthedValue(),
            range->elementsConst(), value->toUInt()); // FIXME: What about signed values?
        param->valuep(cnst);

        return param;
    } else if (type == "AST_MEMORY") {
        auto name = json.find("name").value();

        auto nodes = json.find("nodes");
        assert( (nodes != json.end()) && (nodes->size() == 2) );

        assert(nodes.value()[0].find("type").value() == "AST_RANGE");
        assert(nodes.value()[1].find("type").value() == "AST_RANGE");

        auto range1 = reinterpret_cast<AstRange *>(parseAstTree(nodes.value()[0]));
        assert(range1);
        AstBasicDType *dtype = new AstBasicDType(new FileLine("json"), AstBasicDTypeKwd::LOGIC_IMPLICIT);
        dtype->rangep(range1);

        auto range2 = reinterpret_cast<AstRange *>(parseAstTree(nodes.value()[1]));

        auto dtypearray = new AstUnpackArrayDType(new FileLine("json"), VFlagChildDType(),
            dtype, range2);
        auto var = new AstVar(new FileLine("json"), AstVarType::VAR, name, dtypearray);
        var->childDTypep(dtypearray);
        if (v3Global.opt.trace())
            var->trace(true);
        return var;
    } else if (type == "AST_WIRE") {
        auto name = json.find("name").value();

        AstPort *p = nullptr;
        AstVar *v = nullptr;

        AstBasicDType *dtype = nullptr;

        auto nodes = json.find("nodes");
        if (nodes != json.end()) {
            for (auto itr = nodes->begin() ; itr != nodes->end() ; ++itr) {
                auto type = itr->find("type").value();

                if (type == "AST_RANGE") {
                    auto range = reinterpret_cast<AstRange *>(parseAstTree(itr.value()));
                    assert(range);
                    dtype = new AstBasicDType(new FileLine("json"), VFlagLogicPacked(), range->elementsConst());
                    dtype->rangep(range);
                } else
                    debug(std::cout << "AST_WIRE: Unknown type: " << type << std::endl);
            }
        } else
            dtype = new AstBasicDType(new FileLine("json"), AstBasicDTypeKwd::LOGIC_IMPLICIT);

        auto port = json.find("port");
        if (port != json.end()) {
            p = new AstPort(new FileLine("json"), ++np, name);

            v = new AstVar(new FileLine("json"), AstVarType::PORT, name, dtype);
            auto direction = port.value();
            if (direction == "input") {
                v->declDirection(VDirection::INPUT);
                v->direction(VDirection::INPUT);
            } else if (direction == "output") {
                v->declDirection(VDirection::OUTPUT);
                v->direction(VDirection::OUTPUT);
            }

            p->addNextNull(v);
        } else {
            v = new AstVar(new FileLine("json"), AstVarType::VAR, name, dtype);
        }

        v->childDTypep(dtype);

        if (v3Global.opt.trace())
            v->trace(true);

        if (p)
            return p;
        else
            return v;
    } else if ( (type == "AST_ASSIGN") || (type == "AST_ASSIGN_LE") || (type == "AST_ASSIGN_EQ") ) {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);

        auto lvalue = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto rvalue = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));

        if (type == "AST_ASSIGN") // assign
            return new AstAssignW(new FileLine("json"), lvalue, rvalue);
        if (type == "AST_ASSIGN_LE") // <= (non blocking)
            return new AstAssignDly(new FileLine("json"), lvalue, rvalue);
        if (type == "AST_ASSIGN_EQ") // = (blocking)
            return new AstAssign(new FileLine("json"), lvalue, rvalue);
    } else if (type == "AST_ALWAYS") {
        auto nodes = json.find("nodes");

        AstSenTree *senTree = nullptr;
        AstBegin *begin = nullptr;

        for (auto itr = nodes->begin() ; itr != nodes->end() ; ++itr) {
            auto type = itr->find("type").value();

            if (type == "AST_POSEDGE")
                senTree = reinterpret_cast<AstSenTree *>(parseAstTree(itr.value()));
            else if (type == "AST_BLOCK")
                begin = reinterpret_cast<AstBegin *>(parseAstTree(itr.value()));
            else
                debug(std::cout << "Unkownn type (2): " << type << std::endl);
        }

        AstAlways *astAlways = new AstAlways(new FileLine("json"),
            VAlwaysKwd::ALWAYS, senTree, begin);

        return astAlways;
    } else if (type == "AST_IDENTIFIER") {
        AstParseRef *ref = new AstParseRef(new FileLine("json"), AstParseRefExp::PX_TEXT,
            json.find("name").value(), nullptr, nullptr);

        auto nodes = json.find("nodes");
        if (nodes != json.end()) {
            for (auto itr = nodes->begin() ; itr != nodes->end() ; ++itr) {
                auto type = itr->find("type").value();

                if (type == "AST_RANGE") {
                    auto nodes = itr->find("nodes");
                    if (nodes->size() > 1) {
                        auto range = reinterpret_cast<AstRange *>(parseAstTree(itr.value()));
                        assert(range);
                        debug(std::cout << "AST_IDENTIFIER: " << range->name() << ", " << range->elementsConst() << ", " <<
                            range->msbConst() << ", " << range->lsbConst() << std::endl);
                        AstSel *sel = new AstSel(new FileLine("json"), ref, range->lsbConst(), range->elementsConst());
                        return sel;
                    } else {
                        auto type = nodes.value()[0].find("type").value();
                        debug(std::cout << "Pre: " << type << std::endl);
                        // FIXME: should be more generic
                        assert( (type == "AST_IDENTIFIER") || (type == "AST_CONSTANT") || (type == "AST_SUB") );
                        auto ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes.value()[0]));
                        auto *sel = new AstSelBit(new FileLine("json"), ref, ref1);
                        return sel;
                    }
                } else
                    debug(std::cout << "AST_IDENTIFIER: Unknown type: " << type << std::endl);
            }
        }

        return ref;
    } else if (type == "AST_POSEDGE") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 1);

        assert(nodes[0].find("type").value() == "AST_IDENTIFIER");
        auto *ref = reinterpret_cast<AstSenTree *>(parseAstTree(nodes[0]));

        AstSenItem *senItem = new AstSenItem(new FileLine("json"), AstEdgeType::ET_POSEDGE, ref);
        return new AstSenTree(new FileLine("json"), senItem);
    } else if ( (type == "AST_BLOCK") || (type == "AST_GENBLOCK") ) {
        auto nodes = json.find("nodes");

        auto *begin = new AstBegin(new FileLine("json"), "", nullptr);

        if (nodes != json.end()) {
            for (auto itr = nodes->begin() ; itr != nodes->end() ; ++itr) {
                auto stmtp = reinterpret_cast<AstNode *>(parseAstTree(itr.value()));
                if (stmtp)
                    begin->addStmtsp(stmtp);
            }
        }

        return begin;
    } else if (type == "AST_NEG") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 1);
        auto *ref = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        return new AstNegate(new FileLine("json"), ref);
    } else if (type == "AST_BIT_NOT") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 1);
        auto *ref = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        return new AstNot(new FileLine("json"), ref);
    } else if (type == "AST_BIT_XOR") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[1]));
        return new AstXor(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_BIT_OR") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[1]));
        return new AstOr(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_LOGIC_OR") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[1]));
        return new AstLogOr(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_BIT_AND") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[1]));
        return new AstAnd(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_LOGIC_AND") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[1]));
        return new AstLogAnd(new FileLine("json"), ref1, ref2);
    } else if ( (type == "AST_REDUCE_OR") || (type == "AST_REDUCE_BOOL") ) {
        // TODO: YOSYS doc says AST_REDUCE_BOOL the same as AST_REDUCE_OR, verify it
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 1);
        auto *ref = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        return new AstRedOr(new FileLine("json"), ref);
    } else if (type == "AST_REDUCE_AND") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 1);
        auto *ref = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        return new AstRedAnd(new FileLine("json"), ref);
    } else if (type == "AST_LOGIC_NOT") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 1);
        auto *ref = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        return new AstLogNot(new FileLine("json"), ref);
    } else if (type == "AST_TO_SIGNED") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 1);
        auto *ref = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        return new AstSigned(new FileLine("json"), ref);
    } else if (type == "AST_TO_UNSIGNED") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 1);
        auto *ref = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        return new AstUnsigned(new FileLine("json"), ref);
    } else if (type == "AST_SHIFT_LEFT") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[1]));
        return new AstShiftL(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_SHIFT_RIGHT") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[1]));
        return new AstShiftR(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_SHIFT_SRIGHT") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[1]));
        return new AstShiftRS(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_TERNARY") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 3);
        auto *ref0 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[0]));
        auto *ref1 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[1]));
        auto *ref2 = reinterpret_cast<AstParseRef *>(parseAstTree(nodes[2]));
        return new AstCond(new FileLine("json"), ref0, ref1, ref2);
    } else if (type == "AST_CONCAT") {
        std::vector<AstNode *> parsedNodes;

        auto nodes = json.find("nodes");
        for (auto itr = nodes->begin() ; itr != nodes->end() ; ++itr) {
            auto ref = reinterpret_cast<AstNode *>(parseAstTree(itr.value()));
            parsedNodes.push_back(ref);
        }

        while (parsedNodes.size() >= 2) {
            auto ref0 = parsedNodes.back();
            parsedNodes.pop_back();
            auto ref1 = parsedNodes.back();
            parsedNodes.pop_back();
            auto concat = new AstConcat(new FileLine("json"), ref0, ref1);
            parsedNodes.push_back(concat);
        }

        assert(parsedNodes.size() == 1);
        auto ret = parsedNodes.back();
        parsedNodes.pop_back();
        return ret;
    } else if (type == "AST_REPLICATE") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *rep = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto *ref = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        return new AstReplicate(new FileLine("json"), ref, rep);
    } else if (type == "AST_ADD") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        return new AstAdd(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_SUB") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        return new AstSub(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_EQ") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        return new AstEq(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_GE") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        return new AstGte(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_LE") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        return new AstLte(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_LT") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        return new AstLt(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_NE") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        return new AstNeq(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_MUL") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 2);
        auto *ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto *ref2 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        return new AstMul(new FileLine("json"), ref1, ref2);
    } else if (type == "AST_INITIAL") {
        auto nodes = json.find("nodes");

        AstBegin *begin = nullptr;
        for (auto itr = nodes->begin() ; itr != nodes->end() ; ++itr) {
            auto type = itr->find("type").value();

            if (type == "AST_BLOCK")
                begin = reinterpret_cast<AstBegin *>(parseAstTree(itr.value()));
            else
                debug(std::cout << "Unknown type (2): " << type << std::endl);
        }

        return new AstInitial(new FileLine("json"), begin);
    } else if (type == "AST_CONSTANT") {
        int value = 0;
        int width = 1;

        if (json.find("value") != json.end())
            value = json.find("value").value();

        if (json.find("width") != json.end())
            width = json.find("width").value();

        return new AstConst(new FileLine("json"), AstConst::WidthedValue(), width, value);
    } else if (type == "AST_CASE") {
        auto nodes = json.find("nodes");

        AstNode *exprp = nullptr, *casep = nullptr, *lastcase = nullptr;
        exprp = reinterpret_cast<AstNode *>(parseAstTree(nodes.value()[0]));

        auto itr = nodes->begin(); ++itr;
        for (; itr != nodes->end() ; ++itr) {
            auto ref = reinterpret_cast<AstNode *>(parseAstTree(itr.value()));

            if (!casep)
                casep = ref;

            if (!lastcase)
                lastcase = ref;
            else {
                lastcase->addNextNull(ref);
                lastcase = ref;
            }
        }

        AstCase *caseNode = new AstCase(new FileLine("json"), VCaseType::CT_CASE, exprp, casep);
        return caseNode;
    } else if (type == "AST_GENIF") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 3);

        auto ref0 = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto ref1 = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        auto ref2 = reinterpret_cast<AstNode *>(parseAstTree(nodes[2]));

        auto ref = new AstGenIf(new FileLine("json"), ref0, ref1, ref2);
        auto gen = new AstGenerate(new FileLine("json"), ref);
        return gen;
    } else if (type == "AST_FOR") {
        auto nodes = json.find("nodes").value();
        assert(nodes.size() == 4);

        auto init  = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        auto cond  = reinterpret_cast<AstNode *>(parseAstTree(nodes[1]));
        auto acti  = reinterpret_cast<AstNode *>(parseAstTree(nodes[2]));
        auto block = reinterpret_cast<AstNode *>(parseAstTree(nodes[3]));

        auto loop = new AstWhile(new FileLine("json"), cond, block, acti);
        init->addNextNull(loop);
        return init;
    } else if (type == "AST_COND") {
        auto nodes = json.find("nodes").value();
        debug(std::cout << "AST_COND: nodes.size() " << nodes.size() << std::endl);

        auto cond = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        // e.g. case cond1, cond2: begin ... end;
        for (int i = 1 ; i < (nodes.size() - 1) ; ++i) {
            auto tmp = reinterpret_cast<AstNode *>(parseAstTree(nodes[i]));
            cond->addNextNull(tmp);
        }

        auto ref = reinterpret_cast<AstNode *>(parseAstTree(nodes[nodes.size() - 1]));
        return new AstCaseItem(new FileLine("json"), cond, ref);
    } else if (type == "AST_DEFAULT") {
        /* Used in AST_CASE, shoud return nullptr (default case) */
        auto nodes = json.find("nodes");
        assert(nodes == json.end());
        return nullptr;
    } else if (type == "AST_LOCALPARAM") {
        /* TODO: Merge with AST_PARAMETER */
        auto name = json.find("name").value();
        debug(std::cout << "AST_PARAMETER: Name: " << name << std::endl);

        auto nodes = json.find("nodes").value();
        assert( (nodes.size() == 1) || (nodes.size() == 2) );

        AstRange *range = nullptr;
        if (nodes.size() >= 2) {
            auto type = nodes[1].find("type").value();
            assert(type == "AST_RANGE");
            range = reinterpret_cast<AstRange *>(parseAstTree(nodes[1]));
        }

        AstNode *value = nullptr;
        if (nodes.size() >= 1) {
            auto type = nodes[0].find("type").value();
            if (type == "AST_CONSTANT") {
                AstConst *cnst = reinterpret_cast<AstConst *>(parseAstTree(nodes[0]));
                if (range) {
                    value = new AstConst(new FileLine("json"), AstConst::WidthedValue(),
                        range->elementsConst(), cnst->toUInt()); // FIXME: What about signed values?
                } else {
                    value = new AstConst(new FileLine("json"), AstConst::WidthedValue(),
                        cnst->width(), cnst->toUInt()); // FIXME: What about signed values?
                }
            } else
                value = reinterpret_cast<AstNode *>(parseAstTree(nodes[0]));
        }

        AstBasicDType *dtype = nullptr;
        if (range) {
            dtype = new AstBasicDType(new FileLine("json"), VFlagLogicPacked(), range->elementsConst());
            dtype->rangep(range);
        } else
            dtype = new AstBasicDType(new FileLine("json"), AstBasicDTypeKwd::LOGIC_IMPLICIT);

        // FIXME: AstVarType
        AstVar *param = new AstVar(new FileLine("json"), AstVarType::LPARAM, name, dtype);
        param->childDTypep(dtype);
        param->valuep(value);
        return param;
    } else {
        debug(std::cout << "Unknown type (1): " << type << std::endl);
    }

    return NULL;
}
