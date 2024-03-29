// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common implemenetations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Ast.h"
#include "V3File.h"
#include "V3HierBlock.h"
#include "V3LinkCells.h"
#include "V3Parse.h"
#include "V3ParseSym.h"
#include "V3Stats.h"

#include "UhdmAst.h"
#include <uhdm/uhdm.h>
#include <uhdm/vpi_visitor.h>
#include "uhdm_dump.h"
#include <iostream>

//######################################################################
// V3 Class -- top level

AstNetlist* V3Global::makeNetlist() { return new AstNetlist(); }

void V3Global::clear() {
#ifdef VL_LEAK_CHECK
    if (m_rootp) VL_DO_CLEAR(m_rootp->deleteTree(), m_rootp = nullptr);
#endif
}

void V3Global::shutdown() {
    VL_DO_CLEAR(delete m_hierPlanp, m_hierPlanp = nullptr);  // delete nullptr is safe
}

void V3Global::checkTree() const { rootp()->checkTree(); }

void V3Global::readFiles() {
    // NODE STATE
    //   AstNode::user4p()      // VSymEnt*    Package and typedef symbol names
    const AstUser4InUse inuser4;

    VInFilter filter(v3Global.opt.pipeFilter());
    V3ParseSym parseSyms(v3Global.rootp());  // Symbol table must be common across all parsing

    if (v3Global.opt.uhdmAst()) {
        // Use UHDM frontend
        const V3StringList& vFiles = v3Global.opt.vFiles();
        UHDM::Serializer serializer;
        std::ostringstream uhdm_lines_dump;

        auto coverage_file = v3Global.opt.uhdmCovFile();
        std::vector<AstNodeModule*> modules;

        for (auto file : vFiles) {
            std::vector<vpiHandle> restoredDesigns = serializer.Restore(file);

            if (v3Global.opt.dumpUhdm()) {
                std::cout << UHDM::visit_designs(restoredDesigns) << std::endl;
            }

            /* Parse */
            if (coverage_file != "") {
                /* Report coverage */
                uhdm_lines_dump << UHDM::dump_visited(restoredDesigns);
                std::cout << "Writing coverage report to: " << coverage_file << std::endl;
                std::ofstream coverage_output(coverage_file);
                coverage_output << "UHDM contents:" << std::endl;
                coverage_output << uhdm_lines_dump.str();
                coverage_output << "Visited nodes:" << std::endl;
                modules = UhdmAst::visit_designs(restoredDesigns, coverage_output, &parseSyms);
            } else {
                std::ostringstream dummy;
                modules = UhdmAst::visit_designs(restoredDesigns, dummy, &parseSyms);
            }

            /* Add to design */
            AstNetlist* designRoot = v3Global.rootp();
            for (auto itr = modules.begin(); itr != modules.end(); ++itr) {
                designRoot->addModulep(*itr);
            }
        }
    } else if (v3Global.opt.uhdmAstSv()) {
        // Use UHDM-SV frontend
        const V3StringList& vFiles = v3Global.opt.vFiles();
        V3StringList svFiles;
        V3StringList uhdmFiles;

        for (auto file : vFiles) {
            std::string::size_type ext_idx;
            std::string ext;
            ext_idx = file.rfind('.');

            if (ext_idx != std::string::npos) {
                ext = file.substr(ext_idx + 1);
            } else {
                return;
            }

            if (ext == "sv" || ext == "vlt") {
                svFiles.push_back(file);
            } else if (ext == "uhdm") {
                uhdmFiles.push_back(file);
            } else {
                // return;
            }
        }

        for (auto uhdmFile : uhdmFiles) {
            UHDM::Serializer serializer;
            std::vector<AstNodeModule*> modules;
            std::vector<vpiHandle> restoredDesigns = serializer.Restore(uhdmFile);

            if (v3Global.opt.dumpUhdm()) {
                std::cout << UHDM::visit_designs(restoredDesigns) << std::endl;
            }

            std::ostringstream dummy;
            modules = UhdmAst::visit_designs(restoredDesigns, dummy, &parseSyms);

            AstNetlist* designRoot = v3Global.rootp();
            for (auto itr = modules.begin(); itr != modules.end(); ++itr) {
                designRoot->addModulep(*itr);
            }
        }
        V3Parse parser(v3Global.rootp(), &filter, &parseSyms);

        for (auto svFile : svFiles) {
            parser.parseFile(new FileLine(FileLine::commandLineFilename()), svFile, false,
                             "Cannot find file containing module: ");
        }

        const V3StringSet& libraryFiles = v3Global.opt.libraryFiles();
        for (const string& filename : libraryFiles) {
            parser.parseFile(new FileLine(FileLine::commandLineFilename()), filename, true,
                             "Cannot find file containing library module: ");
        }

    } else {
        // Use standard Verilator frontend
        V3Parse parser(v3Global.rootp(), &filter, &parseSyms);
        // Read top module
        const V3StringList& vFiles = v3Global.opt.vFiles();
        for (const string& filename : vFiles) {
            parser.parseFile(new FileLine(FileLine::commandLineFilename()), filename, false,
                            "Cannot find file containing module: ");
        }

        // Read libraries
        // To be compatible with other simulators,
        // this needs to be done after the top file is read
        const V3StringSet& libraryFiles = v3Global.opt.libraryFiles();
        for (const string& filename : libraryFiles) {
            parser.parseFile(new FileLine(FileLine::commandLineFilename()), filename, true,
                            "Cannot find file containing library module: ");
        }
    }
    // v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("parse.tree"));
    V3Error::abortIfErrors();

    if (!v3Global.opt.preprocOnly()) {
        // Resolve all modules cells refer to
        V3LinkCells::link(v3Global.rootp(), &filter, &parseSyms);
    }
}

string V3Global::debugFilename(const string& nameComment, int newNumber) {
    ++m_debugFileNumber;
    if (newNumber) m_debugFileNumber = newNumber;
    return opt.hierTopDataDir() + "/" + opt.prefix() + "_" + digitsFilename(m_debugFileNumber)
           + "_" + nameComment;
}
string V3Global::digitsFilename(int number) {
    std::stringstream ss;
    ss << std::setfill('0') << std::setw(3) << number;
    return ss.str();
}

void V3Global::dumpCheckGlobalTree(const string& stagename, int newNumber, bool doDump) {
    v3Global.rootp()->dumpTreeFile(v3Global.debugFilename(stagename + ".tree", newNumber), false,
                                   doDump);
    if (v3Global.opt.stats()) V3Stats::statsStage(stagename);
}

const std::string& V3Global::ptrToId(const void* p) {
    auto it = m_ptrToId.find(p);
    if (it == m_ptrToId.end()) {
        std::ostringstream os;
        if (p) {
            os << "(";
            unsigned id = m_ptrToId.size();
            do { os << static_cast<char>('A' + id % 26); } while (id /= 26);
            os << ")";
        } else {
            os << "0";
        }
        it = m_ptrToId.insert(std::make_pair(p, os.str())).first;
    }
    return it->second;
}
