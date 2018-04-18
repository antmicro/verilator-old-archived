// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2017 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************


#include "V3EmitFilter.h"
#include "V3File.h"

#include <sstream>
#include <iomanip>

static void generateFilter(string mod, string var, AstEnumDType *enump) {
    UINFO(2,"generate for: " << var << " in " << mod <<endl);
    AstBasicDType *dtype = enump->basicp()->castBasicDType();
    if (!dtype || dtype->isBitLogic()) {
	UINFO(2, "encountered invalid basic data type");
	return;
    }

    string filename = mod + "_" + var + ".filter";
    V3OutFilterFile file(filename);
    ASTNODE_ITERATE(EnumItem, itemp, enump->itemsp()) {
	AstConst *value = itemp->valuep()->castConst();
	if (value) {
	    std::stringstream ss;
	    ss << setfill('0') << setw(8) << value->toUInt() << " " << itemp->name() << endl;
	    file.puts(ss.str());
	}
    }
}

void V3EmitFilter::emitfilters(AstNetlist *netlist) {
    UINFO(2,__FUNCTION__<<": "<<endl);

    ASTNODE_ITERATE(NodeModule, nodep, v3Global.rootp()->modulesp()) {
	string mod_name = nodep->name();
	for (AstNode* stmtp=nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
	    if (AstVar *var = stmtp->castVar()) {
		string var_name = var->name();
		if (AstRefDType *rdtypep = var->subDTypep()->castRefDType()) {
		    if (AstEnumDType *edtypep = rdtypep->skipRefToEnump()->castEnumDType()) {
			generateFilter(mod_name, var_name, edtypep);
		    }
		}
	    }
	}
    }
}
