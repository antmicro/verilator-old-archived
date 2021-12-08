// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Prepare AST for dynamic scheduler features
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3DynamicScheduler's Transformations:
//
//      Each Delay, TimingControl, Wait:
//          Mark containing task for dynamic scheduling
//          Mark containing process for dynamic scheduling
//      Each Task:
//          If it's virtual, mark it
//      Each task calling a marked task:
//          Mark it for dynamic scheduling
//      Each process calling a marked task:
//          Mark it for dynamic scheduling
//      Each marked process:
//          Wrap its statements into begin...end so it won't get split
//
//      Each TimingControl, Wait:
//          Create event variables for triggering those.
//          For Wait:
//              Transform into:
//                  while (!wait.condp) {
//                      @(vars from wait.condp);
//                  }
//                  wait.bodysp;
//              (process the new TimingControl as specified below)
//          For TimingControl:
//              If waiting on event, leave it as is
//              If waiting on posedge:
//                  Create a posedge event variable for the awaited signal
//              If waiting on negedge:
//                  Create a negedge event variable for the awaited signal
//              If waiting on bothedge:
//                  Split it into posedge and negedge
//                  Create a posedge event variable for the awaited signal
//                  Create a negedge event variable for the awaited signal
//              If waiting on anyedge:
//                  Create a anyedge event variable for the awaited signal
//              For each variable in the condition being waited on:
//                  Create an anyedge event variable for the awaited variable
//
//      Each assignment:
//          If there is an edge event variable associated with the LHS:
//              Create an EventTrigger for this event variable under an if that checks if the edge
//              occurs
//      Each var that could be assigned from the outside (e.g. a clock):
//          If there is an edge event variable associated with it:
//              Create a new Active for this edge with an EventTrigger for this event variable
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3DynamicScheduler.h"
#include "V3Ast.h"

//######################################################################

class DynamicSchedulerWrapProcessVisitor final : public AstNVisitor {
private:
    // NODE STATE
    // AstNodeProcedure::user1()      -> bool.  Set true if shouldn't be split up
    AstUser1InUse m_inuser1;

    // STATE
    AstNode* m_proc = nullptr;
    bool repeat = false;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_proc);
        {
            m_proc = nodep;
            if (!nodep->user1()) {
                iterateChildren(nodep);
                if (nodep->user1()) {
                    // Prevent splitting by wrapping body in an AstBegin
                    auto* bodysp = nodep->bodysp()->unlinkFrBackWithNext();
                    nodep->addStmtp(new AstBegin{nodep->fileline(), "", bodysp});
                }
            }
        }
    }
    virtual void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_proc);
        {
            m_proc = nodep;
            if (!nodep->user1()) {
                if (nodep->isVirtual())
                    nodep->user1u(true);
                else
                    iterateChildren(nodep);
                if (nodep->user1()) repeat = true;
            }
        }
    }
    virtual void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_proc);
        {
            m_proc = nodep;
            if (!nodep->user1()) {
                if (nodep->isVirtual())
                    nodep->user1u(true);
                else
                    iterateChildren(nodep);
                if (nodep->user1()) repeat = true;
            }
        }
    }
    virtual void visit(AstDelay* nodep) override {
        if (m_proc) m_proc->user1u(true);
    }
    virtual void visit(AstTimingControl* nodep) override {
        if (m_proc) m_proc->user1u(true);
    }
    virtual void visit(AstWait* nodep) override {
        if (m_proc) m_proc->user1u(true);
    }
    virtual void visit(AstFork* nodep) override {
        if (m_proc) m_proc->user1u(!nodep->joinType().joinNone());
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        if (m_proc && nodep->taskp()->user1()) m_proc->user1u(true);
    }
    virtual void visit(AstMethodCall* nodep) override {
        if (m_proc && nodep->taskp()->user1()) m_proc->user1u(true);
    }
    virtual void visit(AstCMethodCall* nodep) override {
        if (m_proc && nodep->funcp()->user1()) m_proc->user1u(true);
    }

    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DynamicSchedulerWrapProcessVisitor(AstNetlist* nodep) {
        do {
            repeat = false;
            iterate(nodep);
        } while (repeat);
    }
    virtual ~DynamicSchedulerWrapProcessVisitor() override {}
};

//######################################################################

using VarEdge = std::pair<AstVarScope*, VEdgeType>;
using VarEdgeEventMap = std::map<VarEdge, AstVarScope*>;

class DynamicSchedulerCreateEventsVisitor final : public AstNVisitor {
private:
    // NODE STATE
    // AstVar::user1()      -> bool.  Set true if variable is waited on
    AstUser1InUse m_inuser1;

    // STATE
    using VarScopeSet = std::set<AstVarScope*>;
    VarScopeSet m_waitVars;

public:
    VarEdgeEventMap m_edgeEvents;

private:
    bool m_inTimingControlSens = false;
    bool m_inWait = false;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()
    AstVarScope* getCreateEvent(AstVarScope* vscp, VEdgeType edgeType) {
        UASSERT_OBJ(vscp->scopep(), vscp, "Var unscoped");
        auto it = m_edgeEvents.find(std::make_pair(vscp, edgeType));
        if (it != m_edgeEvents.end()) return it->second;
        string newvarname = (string("__VedgeEvent__") + vscp->scopep()->nameDotless() + "__"
                             + edgeType.ascii() + "__" + vscp->varp()->name());
        auto* newvarp = new AstVar(vscp->fileline(), AstVarType::MODULETEMP, newvarname,
                                   vscp->findBasicDType(AstBasicDTypeKwd::EVENTVALUE));
        vscp->scopep()->modp()->addStmtp(newvarp);
        auto* newvscp = new AstVarScope(vscp->fileline(), vscp->scopep(), newvarp);
        vscp->user1p(newvscp);
        vscp->scopep()->addVarp(newvscp);
        m_edgeEvents.insert(std::make_pair(std::make_pair(vscp, edgeType), newvscp));
        return newvscp;
    }
    AstVarScope* getEvent(AstVarScope* vscp, VEdgeType edgeType) {
        auto it = m_edgeEvents.find(std::make_pair(vscp, edgeType));
        if (it != m_edgeEvents.end()) return it->second;
        return nullptr;
    }

    // VISITORS
    virtual void visit(AstTimingControl* nodep) override {
        VL_RESTORER(m_inTimingControlSens);
        m_inTimingControlSens = true;
        iterateAndNextNull(nodep->sensesp());
        m_inTimingControlSens = false;
        iterateAndNextNull(nodep->stmtsp());
    }
    virtual void visit(AstWait* nodep) override {
        VL_RESTORER(m_inWait);
        m_inWait = true;
        iterateAndNextNull(nodep->condp());
        if (m_waitVars.empty()) {
            if (nodep->bodysp())
                nodep->replaceWith(nodep->bodysp()->unlinkFrBack());
            else
                nodep->unlinkFrBack();
        } else {
            auto fl = nodep->fileline();
            AstNode* senitemsp = nullptr;
            for (auto* vscp : m_waitVars) {
                AstVarScope* eventp = vscp->varp()->dtypep()->basicp()->isEventValue()
                                          ? vscp
                                          : getCreateEvent(vscp, VEdgeType::ET_ANYEDGE);
                senitemsp = AstNode::addNext(
                    senitemsp, new AstSenItem{fl, VEdgeType::ET_ANYEDGE,
                                              new AstVarRef{fl, eventp, VAccess::READ}});
            }
            auto* condp = nodep->condp()->unlinkFrBack();
            auto* timingControlp = new AstTimingControl{
                fl, new AstSenTree{fl, VN_CAST(senitemsp, SenItem)}, nullptr};
            auto* whilep = new AstWhile{fl, new AstLogNot{fl, condp}, timingControlp};
            if (nodep->bodysp()) whilep->addNext(nodep->bodysp()->unlinkFrBack());
            nodep->replaceWith(whilep);
            m_waitVars.clear();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstSenItem* nodep) override {
        if (m_inTimingControlSens) {
            if (nodep->edgeType() == VEdgeType::ET_BOTHEDGE) {
                nodep->addNextHere(nodep->cloneTree(false));
                nodep->edgeType(VEdgeType::ET_POSEDGE);
                VN_CAST(nodep->nextp(), SenItem)->edgeType(VEdgeType::ET_NEGEDGE);
            }
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstVarRef* nodep) override {
        if (m_inWait) {
            nodep->varp()->user1u(1);
            m_waitVars.insert(nodep->varScopep());
        } else if (m_inTimingControlSens) {
            if (!nodep->varp()->dtypep()->basicp()->isEventValue()) {
                nodep->varp()->user1u(1);
                auto edgeType = VN_CAST(nodep->backp(), SenItem)->edgeType();
                nodep->varScopep(getCreateEvent(nodep->varScopep(), edgeType));
                nodep->varp(nodep->varScopep()->varp());
            }
        }
    }

    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DynamicSchedulerCreateEventsVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~DynamicSchedulerCreateEventsVisitor() override {}
};

//######################################################################

class DynamicSchedulerAddTriggersVisitor final : public AstNVisitor {
private:
    // NODE STATE
    // AstVar::user1()      -> bool.  Set true if variable is waited on
    // AstUser1InUse    m_inuser1;      (Allocated for use in DynamicSchedulerCreateEventsVisitor)
    // AstNode::user2()      -> bool.  Set true if node has been processed
    AstUser2InUse m_inuser2;

    // STATE
    VarEdgeEventMap m_edgeEvents;
    using VarMap = std::map<const std::pair<AstNodeModule*, string>, AstVar*>;
    VarMap m_modVarMap;  // Table of new var names created under module
    size_t m_count = 0;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstVarScope* getCreateVar(AstVarScope* oldvarscp, const string& name) {
        UASSERT_OBJ(oldvarscp->scopep(), oldvarscp, "Var unscoped");
        AstVar* varp;
        AstNodeModule* addmodp = oldvarscp->scopep()->modp();
        // We need a new AstVar, but only one for all scopes, to match the new AstVarScope
        const auto it = m_modVarMap.find(make_pair(addmodp, name));
        if (it != m_modVarMap.end()) {
            // Created module's AstVar earlier under some other scope
            varp = it->second;
        } else {
            varp = new AstVar{oldvarscp->fileline(), AstVarType::BLOCKTEMP, name,
                              oldvarscp->varp()};
            varp->dtypeFrom(oldvarscp);
            addmodp->addStmtp(varp);
            m_modVarMap.emplace(make_pair(addmodp, name), varp);
        }
        AstVarScope* varscp = new AstVarScope{oldvarscp->fileline(), oldvarscp->scopep(), varp};
        oldvarscp->scopep()->addVarp(varscp);
        return varscp;
    }

    AstVarScope* getEvent(AstVarScope* vscp, VEdgeType edgeType) {
        auto it = m_edgeEvents.find(std::make_pair(vscp, edgeType));
        if (it != m_edgeEvents.end()) return it->second;
        return nullptr;
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) override {
        if (nodep->user2SetOnce()) return;
        if (auto* varrefp = VN_CAST(nodep->lhsp(), VarRef)) {
            auto fl = nodep->fileline();
            if (varrefp->varp()->user1u().toInt() == 1) {
                auto* newvscp
                    = getCreateVar(varrefp->varScopep(), "__Vprevval" + std::to_string(m_count++)
                                                             + "__" + varrefp->name());
                nodep->addHereThisAsNext(
                    new AstAssign{fl, new AstVarRef{fl, newvscp, VAccess::WRITE},
                                  new AstVarRef{fl, varrefp->varScopep(), VAccess::READ}});

                if (auto* eventp = getEvent(varrefp->varScopep(), VEdgeType::ET_POSEDGE)) {
                    nodep->addNextHere(new AstIf{
                        fl,
                        new AstAnd{fl,
                                   new AstLogNot{fl, new AstVarRef{fl, newvscp, VAccess::READ}},
                                   new AstVarRef{fl, varrefp->varScopep(), VAccess::READ}},
                        new AstEventTrigger{fl, new AstVarRef{fl, eventp, VAccess::WRITE}}});
                }

                if (auto* eventp = getEvent(varrefp->varScopep(), VEdgeType::ET_NEGEDGE)) {
                    nodep->addNextHere(new AstIf{
                        fl,
                        new AstAnd{fl, new AstVarRef{fl, newvscp, VAccess::READ},
                                   new AstLogNot{fl, new AstVarRef{fl, varrefp->varScopep(),
                                                                   VAccess::READ}}},
                        new AstEventTrigger{fl, new AstVarRef{fl, eventp, VAccess::WRITE}}});
                }

                if (auto* eventp = getEvent(varrefp->varScopep(), VEdgeType::ET_ANYEDGE)) {
                    nodep->addNextHere(new AstIf{
                        fl,
                        new AstNeq{fl, new AstVarRef{fl, newvscp, VAccess::READ},
                                   new AstVarRef{fl, varrefp->varScopep(), VAccess::READ}},
                        new AstEventTrigger{fl, new AstVarRef{fl, eventp, VAccess::WRITE}}});
                }
            }
        }
    }
    virtual void visit(AstVarScope* nodep) override {
        AstVar* varp = nodep->varp();
        if (varp->user1u().toInt() == 1
            && (varp->isUsedClock() || (varp->isSigPublic() && varp->direction().isNonOutput()))) {
            auto fl = nodep->fileline();
            for (auto edgeType :
                 {VEdgeType::ET_ANYEDGE, VEdgeType::ET_POSEDGE, VEdgeType::ET_NEGEDGE}) {
                if (auto* eventp = getEvent(nodep, edgeType)) {
                    auto* activep = new AstActive{
                        fl, "",
                        new AstSenTree{fl,
                                       new AstSenItem{fl, edgeType,
                                                      new AstVarRef{fl, nodep, VAccess::READ}}}};
                    activep->sensesStorep(activep->sensesp());
                    auto* ifp = new AstIf{
                        fl, new AstLogNot{fl, new AstVarRef{fl, eventp, VAccess::READ}},
                        new AstEventTrigger{fl, new AstVarRef{fl, eventp, VAccess::WRITE}}};
                    activep->addStmtsp(ifp);
                    nodep->addNextHere(activep);
                }
            }
        }
    }

    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DynamicSchedulerAddTriggersVisitor(
        DynamicSchedulerCreateEventsVisitor& createEventsVisitor, AstNetlist* nodep)
        : m_edgeEvents(std::move(createEventsVisitor.m_edgeEvents)) {
        iterate(nodep);
    }
    virtual ~DynamicSchedulerAddTriggersVisitor() override {}
};

//######################################################################
// DynamicScheduler class functions

void V3DynamicScheduler::wrapProcesses(AstNetlist* nodep) {
    { DynamicSchedulerWrapProcessVisitor visitor(nodep); }
    V3Global::dumpCheckGlobalTree("dsch_proc", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3DynamicScheduler::prepEvents(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    UINFO(2, "  Add Edge Events...\n");
    DynamicSchedulerCreateEventsVisitor createEventsVisitor(nodep);
    V3Global::dumpCheckGlobalTree("dsch_make_events", 0,
                                  v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
    UINFO(2, "  Add Edge Event Triggers...\n");
    DynamicSchedulerAddTriggersVisitor addTriggersVisitor(createEventsVisitor, nodep);
    V3Global::dumpCheckGlobalTree("dsch_add_triggers", 0,
                                  v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
    UINFO(2, "  Done.\n");
    V3Global::dumpCheckGlobalTree("dsch_prep_events", 0,
                                  v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
