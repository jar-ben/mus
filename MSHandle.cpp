#include "MSHandle.h"
#include <sstream>
#include <fstream>
#include <iostream>
#include <ctime>
#include <algorithm>
#include <random>
#include <stdlib.h>   
#include <time.h>   


using namespace Minisat;
using namespace std;

void print_formula2(std::vector<bool> f){
	for(int i = 0; i < f.size(); i++)
		std::cout << int(f[i]);
	std::cout << std::endl;
}

void print_clause(vector<int> cl){
	for(auto &l: cl)
		cout << l << " ";
	cout << endl;
}

Lit itoLit(int i){
	bool sign = i < 0;
	int var = (sign)? -i-1 : i-1;
	return (sign) ? ~mkLit(var) : mkLit(var);
}

int Littoi(Lit l){
	return (var(l)+1) * (sign(l) ? -1 : 1);
}

vector<int>  convert_clause(string clause){
	vector<int> ret;
	istringstream is(clause);
	int n;
	while(is >> n)
		ret.push_back(n);
	ret.pop_back();
	return ret;
}

MSHandle::MSHandle(string filename):SatSolver(filename){
	solver = new Solver();
//        solver->phase_saving = 2;
	vars = 0;
	parse_dimacs(filename);
	dimension = clauses.size();
	srand (time(NULL));
	rotated_crits = 0;
	flip_edges_computed.resize(dimension, false);
	flip_edges.resize(dimension);
	flip_edges_flatten.resize(dimension);
}

MSHandle::~MSHandle(){
	delete solver;
}

void MSHandle::compute_flip_edges(int c){
	if(flip_edges_computed[c]) return;
	flip_edges_computed[c] = true;

	vector<bool> flatten(dimension, false);
	for(auto lit: clauses[c]){
		vector<int> edges;
		if(lit > 0){
			for(auto &h: hitmap_neg[lit - 1]){
				if(h != c){
					edges.push_back(h);
					flatten[h] = true;
				}
			}
		}
		else{
			for(auto &h: hitmap_pos[(-1 * lit) - 1]){
				if(h != c){
					edges.push_back(h);			
					flatten[h] = true;
				}
			}
		}
		flip_edges[c].push_back(edges);
	}
	for(int i = 0; i < dimension; i++)
		if(flatten[i])
			flip_edges_flatten[c].push_back(i);
}

bool MSHandle::add_clause(vector<int> cl){
	std::sort(cl.begin(), cl.end());
	vector<int> copy = cl; 
	copy.pop_back(); //get rid of control variable
	clauses.push_back(cl);
	clauses_map[copy] = clauses.size() - 1; //used for manipulation with single MUS extractions (muser2, dmuser)
	vec<Lit> msClause;
	for(auto &lit: cl)
		msClause.push(itoLit(lit));		

	for(auto &lit: copy){
		if(lit > 0)
			hitmap_pos[lit - 1].push_back(clauses.size() - 1);
		else
			hitmap_neg[(-1 * lit) - 1].push_back(clauses.size() - 1);
	}
	return solver->addClause(msClause);
}

bool MSHandle::add_unit(int lit){
	return solver->addClause(itoLit(lit));
}

bool MSHandle::parse_dimacs(string path){
        ifstream infile(path, ifstream::in);
        if (!infile.is_open()){
		cout << endl << "wrong input file" << endl;
		exit(1);
	}

        string line;
	vector<int> clause;
	string pom;
        while (getline(infile, line))
        {
                if (line[0] == 'p'){
			istringstream is(line);
			is >> pom;	// p
			is >> pom;	// cnf
			is >> vars;	//number of variables	
		}
                else if(line[0] == 'c')
			continue;
		else if(clauses_unique_map.find(line) != clauses_unique_map.end()){
			cout << "a duplicate clause found in the input formula" << endl;
			continue;		
		}
		else{
			clauses_str.push_back(line);
			clauses_unique_map[line] = clauses_str.size() - 1;
		}
        }
	hitmap_pos.resize(vars);
	hitmap_neg.resize(vars);
	for(int i = 0; i < vars; i++){
		solver->newVar();	// clause variables
	}
	for(int i = 0; i < clauses_str.size(); i++)
		solver->newVar(lbool(uint8_t(1)), true);	// control variables
	for(size_t i = 0; i < clauses_str.size(); i++){
		clauses_string.push_back(clauses_str[i]);
		clause = convert_clause(clauses_str[i]);
		clause.push_back(vars + i + 1);	//control variable
		add_clause(clause); //add clause to the solver
	}
	return true;
}

bool MSHandle::validate_model(vector<bool> model, vector<bool> subset, vector<bool> original){
	for(int i = 0; i < subset.size(); i++){
		if(subset[i]){
			//cout << endl << endl;
			bool ok = false;
			for(int j = 0; j < clauses[i].size() - 1; j++){
				int lit = clauses[i][j];
				//cout << "lit: " << lit << endl;
				if(lit > 0 && model[lit - 1])
					ok = true;
				if(lit < 0 && !model[(-1 * lit) - 1])
					ok = true;
			}
			if(!ok){
				cout << "invalid model" << endl;
				cout << "clause: " << clauses_str[i] << endl;
				cout << "formula:" << endl;
				for(int i = 0; i < dimension; i++){
					if(subset[i])
						cout << clauses_str[i] << endl;
				}
				cout << "vars: " << vars << endl;
				cout << "model:" << endl;
				for(int i = 0; i < vars; i++)
					if(model[i])
						cout << i << ": true" << endl;
					else
						cout << i << ": false" << endl;
				if(original[i]) cout << "cointained in the original one" << endl;
				else cout << "not cointained in the original one" << endl;
				exit(1);
			}
		}
	}
}

vector<bool> MSHandle::model_extension(vector<bool> subset, vector<bool> model){
	int flipped = 0;
	vector<bool> extension = subset;
	for(int i = 0; i < extension.size(); i++){
		if(!extension[i]){
			for(int j = 0; j < clauses[i].size() - 1; j++){
				int lit = clauses[i][j];
				if(lit > 0 && model[lit - 1]){
					extension[i] = true;
					flipped++;
					break;
				}
				else if(lit < 0 && !model[(-1 * lit) - 1]){
					extension[i] = true;
					flipped++;
					break;
				}				
			}
		}
	}
	return extension;
}

void MSHandle::criticals_rotation(vector<bool>& criticals, vector<bool> subset){
	for(int c = 0; c < dimension; c++){
		if(subset[c] && !criticals[c]){ //c is not known to be critical yet
			compute_flip_edges(c); //TODO: better encansulape
			for(int i = 0; i < flip_edges[c].size(); i++){			
				vector<int> flip_edge_groups = flip_edges[c][i]; //edges grouped by literals	

				//count clauses with the same literal and try to rotate if c is the only one
				int literal = clauses[c][i];
				bool only_clause = true;
				if(literal > 0){
					for(auto &hit: hitmap_pos[literal - 1]){
						if(subset[hit] && hit != c) {only_clause = false; break; }
					}
				}			
				else{
					for(auto &hit: hitmap_neg[(-1 * literal) - 1]){
						if(subset[hit] && hit != c) {only_clause = false; break; }
					}
				}
				// c is the only clause containing literal, so if any of the neighbours in the flip grap is critical, then c is necessarily also critical
				if(only_clause){
					for(auto &edge: flip_edge_groups){ 
						if(criticals[edge]){ criticals[c] = true; break; } 
					}	
				}
			}
		}
	}
}


//checks only guaranteed edges
int MSHandle::model_rotation(vector<bool>& criticals, int critical, vector<bool>& subset, vector<bool>& model, vector<vector<bool>>& model_extensions){
	//return model_rotation_beta(criticals, critical, subset, model, model_extensions);

	int rotated = 0;
	compute_flip_edges(critical); //TODO: better encansulape
	for(int i = 0; i < flip_edges[critical].size(); i++){
		vector<int> literal_edges = flip_edges[critical][i]; //edges grouped by literals
		int literal = clauses[critical][i];
		int count = 0;
		vector<bool> extension_seed = subset;	
		for(auto &c: literal_edges){ //individual edges
			if(subset[c]){ //there is a flip edge from critical to c
				count++;
				extension_seed[c] = false;
			}
		}
		int lit_index = (literal > 0)? (literal - 1) : ((-1 * literal) - 1);
		model[lit_index] = !model[lit_index];
		vector<bool> extension = model_extension(extension_seed, model);

		// check if a critical was found
		int count2 = 0;
		int last = -1;
		for(auto &c: literal_edges){ //individual edges
			if(subset[c]){ //there is a flip edge from critical to c
				if(!extension[c]){
					count2++;
					last = c;
				}
			}
		}
		if(count2 == 1 && !criticals[last]){ //new critical found
			rotated_crits++;
			rotated++;
			criticals[last] = true;
			rotated += model_rotation(criticals, last, subset, model, model_extensions);
		}		
		model_extensions.push_back(extension);
		model[lit_index] = !model[lit_index];
	}	
	return rotated;
}

//post extension
int MSHandle::model_rotation_beta(vector<bool>& criticals, int critical, vector<bool>& subset, vector<bool>& model, vector<vector<bool>>& model_extensions){
	int rotated = 0;
	compute_flip_edges(critical); //TODO: better encansulape
	for(int i = 0; i < flip_edges[critical].size(); i++){
		int literal = clauses[critical][i];
		int lit_index = (literal > 0)? (literal - 1) : ((-1 * literal) - 1);				
		model[lit_index] = !model[lit_index]; //rotate model
		vector<int> literal_edges = flip_edges[critical][i]; //edges grouped by literals
		int count = 0;
		int last = -1;
		vector<bool> extension_seed = subset;	
		for(auto &c: literal_edges){ //individual edges
			if(subset[c]){ //there is a flip edge from critical to c
				bool sat = false;
				for(int j = 0; j < clauses[c].size() - 1; j++){ // be carefull of the "- 1", there is a control literal at the end of each clause
					int lit = clauses[c][j];		
					if(lit != literal * -1 && ((lit > 0 && model[lit - 1]) || (lit < 0 && !model[(-1 * lit) - 1]))){
						sat = true;
						break;
					}
				}
				if(!sat){ count++; extension_seed[c] = false; last = c; }
			}
		}

		if(count == 1 && !criticals[last]){			
			vector<bool> extension = model_extension(extension_seed, model);
			model_extensions.push_back(extension);
			rotated_crits++;
			criticals[last] = true;
			model_rotation_beta(criticals, last, subset, model, model_extensions);	
		}
		
		model[lit_index] = !model[lit_index]; //undo rotation
	}	
	return rotated;
}

//post extension
int MSHandle::critical_rotation(vector<bool>& criticals, int critical, vector<bool>& model, vector<int>& new_criticals){
	int rotated = 0;
	compute_flip_edges(critical); //TODO: better encansulape
	for(int i = 0; i < flip_edges[critical].size(); i++){
		int literal = clauses[critical][i];
		int lit_index = (literal > 0)? (literal - 1) : ((-1 * literal) - 1);				
		model[lit_index] = !model[lit_index]; //rotate model
		vector<int> &literal_edges = flip_edges[critical][i]; //edges grouped by literals
		int count = 0;
		int last = -1;	
		for(auto &c: literal_edges){ //individual edges
			bool sat = false;
			for(int j = 0; j < clauses[c].size() - 1; j++){ // be carefull of the "- 1", there is a control literal at the end of each clause
				int lit = clauses[c][j];		
				if(lit != literal * -1 && ((lit > 0 && model[lit - 1]) || (lit < 0 && !model[(-1 * lit) - 1]))){
					sat = true;
					break;
				}
			}
			if(!sat){ count++; last = c; }
		}
		bool new_crit = std::find(new_criticals.begin(), new_criticals.end(), last) == new_criticals.end() && !criticals[last];
		if(count == 1 && new_crit){			
			new_criticals.push_back(last);
			rotated_crits++;
			rotated++;
			rotated += critical_rotation(criticals, last, model, new_criticals);	
		}
		
		model[lit_index] = !model[lit_index]; //undo rotation
	}	
	return rotated;
}


// check formula for satisfiability using miniSAT
// the core and grow variables controls whether to return an unsat core or model extension, respectively
bool MSHandle::solve(vector<bool>& controls, bool unsat_improve, bool sat_improve){
	checks++;
	if(sat_solver == "glucose")
		return solve_glucose(controls, sat_improve, unsat_improve);
	if(sat_solver == "lingeling")
		return solve_lingeling(controls);
	vec<Lit> lits;
	for(unsigned int i = 0; i < controls.size(); i++){
		if(controls[i])
			lits.push(itoLit((i + vars + 1) * (-1)));
		else
			lits.push(itoLit(i + vars + 1 ));
	}
	bool sat = solver->solve(lits);
	if(sat && sat_improve){ // extract model extension		
		for(int f = 0; f < controls.size(); f++){
			if(!controls[f]){
				for(int l = 0; l < clauses[f].size() - 1; l++){
					if(clauses[f][l] > 0){
						if(solver->model[clauses[f][l] - 1] == l_True){
							controls[f] = true;
							break;
						}
					}
					else{
						if(solver->model[-1 * clauses[f][l] - 1] == l_False){
							controls[f] = true;
							break;
						}
					}
				}
			}
		}
	}			
	else if(!sat && unsat_improve){ // extract unsat core
		vector<bool> core = vector<bool> (dimension, false);		
	        for (int i = 0 ; i < solver->conflict.size() ; i++) 
			core[var(solver->conflict[i]) - vars] = true;
		controls = core;		

	}				
	return sat;
}

vector<bool> MSHandle::get_model(){
	vector<bool> model(vars, false);
	for(int i = 0; i < vars; i++){
		if(solver->model[i] == l_True)
			model[i] = true;
		else if(solver->model[i] == l_False)
			model[i] = false;
		else
			cout << "literal not evaluated " << i << endl;
	}
	return model;
}

// check formula for satisfiability using glucose
// the core and grow variables controls whether to return an unsat core or model extension, respectively
bool MSHandle::solve_glucose(vector<bool>& formula, bool sat_improve, bool unsat_improve){
	std::cout << "using glucose" << std::endl;
	std::string export_path = "exp.cnf";
	std::string drup_path = "drup";
	export_formula(formula, export_path);

	stringstream cmd;	
	if(unsat_improve)		
		cmd << "./glucose-simp -certified -certified-output=" << drup_path << " " << export_path << " > /dev/null";
	else
		cmd << "./glucose-simp " << export_path << " > /dev/null";
	int status = system(cmd.str().c_str());
	//2560 -- satisfiable
	//5120 -- unsatisfiable
	bool sat = status == 2560;
	if(status != 2560 && status != 5120){
		std::cout << "invalid glucose return value: " << status << std::endl;
		exit(1);
	}

	if(!sat && unsat_improve){
		std::string core_path = "core.cnf";
		stringstream drup_cmd;
		drup_cmd << "./drup-trim " << export_path << " " << drup_path << " -c " << core_path << " > /dev/null";
		int core_status = system(drup_cmd.str().c_str());
		//0 -- core found
		//256 -- trivial unsat, no core returned		
		std::cout << "drup-trim status: " << core_status << std::endl;
		if(core_status == 0){
			formula = import_formula(core_path);
		}		
	}
		
	return sat;
}

bool MSHandle::solve_lingeling(vector<bool>& formula){
//	std::cout << "using lingeling" << std::endl;
	std::string export_path = "exp.cnf";
	std::string drup_path = "drup";
	export_formula(formula, export_path);

	stringstream cmd;
	cmd << "./lingeling " << export_path << " > /dev/null";
	int status = system(cmd.str().c_str());
	//10 -- satisfiable
	//20 -- unsatisfiable
	bool sat = status == 2560;
//	cout << "status:" << status << endl;
//	if(status != 10 && status != 20){
//		std::cout << "invalid lingeling return value: " << status << std::endl;
//		exit(1);
//	}
	return sat;
}


//
// MUSer2 / dmuser helper functions
//
void MSHandle::export_formula(vector<bool> f, string filename){
	int formulas = std::count(f.begin(), f.end(), true);

	ofstream file;
	file.open(filename);
	file << "p cnf " << vars << " " << formulas << "\n";
	for(int i = 0; i < f.size(); i++)
		if(f[i]){
			file << clauses_str[i] << "\n";
		}
	file.close();
}

void MSHandle::export_formula_crits(vector<bool> f, string filename, vector<bool> crits){
	int formulas = std::count(f.begin(), f.end(), true);

	ofstream file;
	file.open(filename);
	file << "p gcnf " << vars << " " << formulas << " " << formulas << "\n";
	for(int i = 0; i < f.size(); i++)
		if(f[i] && crits[i]){
			file << "{0} " << clauses_str[i] << "\n";
		}
	int group = 1;
	for(int i = 0; i < f.size(); i++)
		if(f[i] && !crits[i]){
			file << "{" << group++ << "} " << clauses_str[i] << "\n";
		}
	file.close();
}

vector<bool> MSHandle::import_formula_crits(string filename){
	ifstream file(filename, ifstream::in);
	vector<bool> f(dimension,false);
	vector<int> c;
	string line;
	string grp;	
	while (getline(file, line))
	{
		if (line[0] == 'c' || line[0] == 'p' || line.empty())
			continue;
		c.clear();
		for(int i = 0; i < line.length(); i++){
			if(line[i] == '}'){
				line.erase(0,i + 1);
				break;
			}
		}
		istringstream is(line);	
		int lit;
		while(is >> lit){
			c.push_back(lit);
		}
		c.pop_back(); // the last literal in .cnf file is a dummy "0"
		std::sort(c.begin(), c.end());
		f[clauses_map[c]] = true;		
	}	
	return f;
}

vector<bool> MSHandle::import_formula(string filename){
	ifstream file(filename, ifstream::in);
	vector<bool> f(dimension,false);
	vector<int> c;
	string line;
	string grp;	
	while (getline(file, line))
	{
		if (line[0] == 'c' || line[0] == 'p' || line.empty())
			continue;
		c.clear();
		istringstream is(line);	
		int lit;
		while(is >> lit){
			c.push_back(lit);
		}
		c.pop_back(); // the last literal in .cnf file is a dummy "0"
		std::sort(c.begin(), c.end());
		f[clauses_map[c]] = true;		
	}	
	return f;
}

vector<bool> MSHandle::shrink_model_extension(std::vector<bool> &f, std::vector<bool> &crits, std::vector<std::vector<bool>>& extensions){
	vector<bool> mus = f;
	vector<bool> copy;
	for(int i = 0; i < dimension; i++){
		if(mus[i] && !crits[i]){
			mus[i] = false;
			if(solve(mus, true, false)){	
				copy = mus;
				for(int f = 0; f < dimension; f++){
					if(!mus[f]){
						for(int l = 0; l < clauses[f].size() - 1; l++){
							if(clauses[f][l] > 0){
								if(solver->model[clauses[f][l] - 1] == l_True){
									copy[f] = true;
									break;
								}
							}
							else{
								if(solver->model[-1 * clauses[f][l] - 1] == l_False){
									copy[f] = true;
									break;
								}
							}
						}
					}
				}
				extensions.push_back(copy);
				mus[i] = true;
			}//end if solve
		}
	}
	return mus;
}

int MSHandle::muser_output(std::string filename){
	ifstream file(filename, ifstream::in);
	std::string line;
	while (getline(file, line))
	{
		if (line.find("c Calls") != std::string::npos){
			std::string calls = line.substr(line.find(":") + 2, line.size()); // token is "scott"
			return atoi(calls.c_str());
		}
	}	
	return 0;
}

vector<bool> MSHandle::shrink_api_muser(vector<bool> &f, vector<bool> crits){
	cout << "shrinking api muser" << endl;
	muser2 m;
	m.init_all();
	m.set_verbosity(0);

	for(int i = 0; i < dimension; i++){
		if(f[i]){
			if(crits[i])
				m.add_clause(&clauses[i][0], &clauses[i][clauses[i].size() - 2], 0); //clauses[i] contains the clause including the trailing control variable, thus that "-2"
			else
				m.add_clause(&clauses[i][0], &clauses[i][clauses[i].size() - 2], i + 1); //clauses[i] contains the clause including the trailing control variable, thus that "-2"
		}
	}

	m.init_run();
	m.compute_gmus();
	m.reset_run();

	vector<bool> mus(dimension, false);
	const std::vector<muser2::gid>& gmus = m.gmus_gids();	
	for(auto &cl: gmus)
		mus[cl - 1] = true;
	for(int i = 0; i < dimension; i++)
		if(crits[i])
			mus[i] = true;
	return mus;
}

// implementation of the shrinking procedure
// based on the value of basic_shrink employes either muser2 or dmuser
vector<bool> MSHandle::shrink(std::vector<bool> &f, std::vector<bool> crits){
	cout << "shrinking dimension " << std::count(f.begin(), f.end(), true) << endl;
	if(shrink_alg == "custom")
		return SatSolver::shrink(f, crits); //shrink with unsat cores
	if(shrink_alg == "api_muser")
		return shrink_api_muser(f, crits);
	std::random_device rd; 
	std::mt19937 eng(rd());
	std::uniform_int_distribution<> distr(1, 1000000000); 
	int hash = distr(eng);

	stringstream exp;			
	exp << "./f_" << hash << ".cnf";			
	//export_formula(f, exp.str());
	export_formula_crits(f, exp.str(), crits);	

	if(shrink_alg == "dmuser"){
		return shrink_dmuser(exp.str(), hash);
	}
	if(shrink_alg == "mcsmus"){
		return shrink_mcsmus(exp.str(), hash);
	}
	else{
		return shrink_muser(exp.str(), hash);
	}
}

vector<bool> MSHandle::shrink_muser(string input, int hash){
	stringstream cmd, muser_out, imp;
	muser_out << "./f_" << hash << "_output";
	imp << "./f_" << hash << "_mus";
	cmd << "./muser2-para -grp -wf " << imp.str() << " " << input << " > " << muser_out.str();// */ " > /dev/null";
//	std::cout << cmd.str() << endl;
	int status = system(cmd.str().c_str());
	if(status < 0){
		std::cout << "Invalid muser return code" << std::endl; exit(0);
	}
	imp << ".gcnf";
	vector<bool> mus = import_formula_crits(imp.str());
	int sat_calls = muser_output(muser_out.str());	
//	checks += sat_calls;
	remove(imp.str().c_str());
	remove(muser_out.str().c_str());
	remove(input.c_str());
	return mus;
}

//todo
vector<bool> MSHandle::shrink_dmuser(string input, int hash){
	vector<bool> mus;
	remove(input.c_str());
	return mus;
}

vector<bool> MSHandle::shrink_mcsmus(string input, int hash){
	stringstream cmd, muser_out, imp;
	muser_out << "./f_" << hash << "_output";
	imp << "./f_" << hash << ".mus.1.cnf";
	cmd << "./mcsmus -print-muses-cnf " << input << " > " << muser_out.str(); //" > /dev/null";
	int status = system(cmd.str().c_str());
	vector<bool> mus = import_formula(imp.str());
	cout << imp.str() << endl;
//	int sat_calls = muser_output(muser_out.str());	
//	checks += sat_calls;
	remove(imp.str().c_str());
	remove(muser_out.str().c_str());
	remove(input.c_str());
	return mus;
}



