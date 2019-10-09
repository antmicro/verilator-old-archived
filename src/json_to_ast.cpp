#include "json_to_ast.hpp"
#include "json.hpp"
#include <fstream>
#include <stdexcept>
#include <sstream>
#include <iostream>
#include <vector>

namespace json_to_ast
{

void load(AstNetlist *design_root, const std::string &filepath)
{
    if (design_root == nullptr)
        throw std::invalid_argument("design root cannot be a nullptr");

    std::ifstream filein(filepath);
    if (!filein)
        throw std::runtime_error(filepath + " - input file does not exist");

    //todo better file reading
    std::stringstream ss;
    ss << filein.rdbuf();

    nlohmann::json json_ast = nlohmann::json::parse(ss.str());
    if (json_ast.empty())
        throw std::invalid_argument("input json is empty");

    //instantiate the module
    auto modules_iter = json_ast.find("modules");
    if (modules_iter == json_ast.end())
        throw std::invalid_argument("Expected \"modules\" json member");

    nlohmann::json &modules_json = *modules_iter;

    if (modules_json.empty())
        throw std::invalid_argument("Expected \"modules\" not to be empty");

    AstModule *module = new AstModule(new FileLine("module poc"), modules_json.begin().key());
    design_root->addModulep(module);

    nlohmann::json &top_module_json = *modules_json.begin();

    if (top_module_json.empty())
        throw std::invalid_argument("Expected module \"" + modules_json.begin().key() + "\" not to be empty");

    //parse ports
    {
        std::vector<AstPort *> ports;
        auto iter = top_module_json.find("ports");
        if (iter == top_module_json.end())
            throw std::invalid_argument("Expected \"ports\" json member");
        nlohmann::json &ports_json = *iter;
        for (auto it = ports_json.begin(); it != ports_json.end(); ++it)
        {
            printf("Port %s\n", it.key().c_str());
            nlohmann::json &port_specification = it.value();
            if (port_specification.empty())
                throw std::invalid_argument("Port specification for \"" + it.key() + "\" is empty");

            auto direction_it = port_specification.find("direction");
            if (direction_it == port_specification.end())
                throw std::invalid_argument("Direction for port \"" + it.key() + "\" is missing");

            std::string direction = direction_it->get<std::string>();
            /*if (direction == "input")
            AstVar* v1 = new AstVar(new FileLine("var1"), AstVarType::WIRE, "c",VFlagChildDType(), basicdtype1);
                ports.push_back(new AstPort(new FileLine("port1"), 1, "c"));*/
        }
    }
    AstPort *p1 = new AstPort(new FileLine("port1"), 1, "c");
    AstPort *p2 = new AstPort(new FileLine("port2"), 2, "d");
    AstPort *p3 = new AstPort(new FileLine("port3"), 3, "q");

    //for (const auto &elem : modules_json)
    //std::cout << modules_json.begin().key<< std::endl;

    //after it's done remove this
    puts("TODO exiting");
    exit(0);
}

} // namespace json_to_ast