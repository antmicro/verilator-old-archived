import os
import sys
from hdlConvertorAst.to.json import ToJson
import json

from hdlConvertorAst.language import Language
from hdlConvertor import HdlConvertor

if len(sys.argv) < 2:
    print("No input files")
    sys.exit(1)

include_dirs = []
c = HdlConvertor()
# note that there is also Language.VERILOG_2005, Language.SYSTEM_VERILOG_2017 and others
d = c.parse(sys.argv[1:], Language.VHDL, include_dirs, hierarchyOnly=False, debug=True)

tj = ToJson()
j = tj.visit_HdlContext(d)
# pretty print json
print(json.dumps(j, sort_keys=True,
                     indent=2, separators=(',', ': ')))

