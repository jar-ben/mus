#include "Solver.h"
#include "misc.h"
#include <algorithm>
#include <math.h>
#include <functional>
#include <random>

bool is_subset2(std::vector<bool> &a, std::vector<bool> &b){
	int dimension = a.size();
	for(int i = 0; i < dimension; i++)
		if(a[i] && !b[i])
			return false;
	return true;
}

bool is_subset2(std::vector<int> &a, std::vector<bool> &b){
	for(auto &constraint: a)
		if(!b[constraint])
			return false;
	return true;
}


Solver::Solver(string filename, int var, bool vis, string s_solver){
        isValidExecutions = 0;
        variant = var;
	sat_solver = s_solver;
	if(ends_with(filename, "smt2")){
		satSolver = new Z3Handle(filename); 
		domain = "smt";
	}
	else if(ends_with(filename, "cnf")){
		satSolver = new MSHandle(filename);
		domain = "sat";
	}
	else if(ends_with(filename, "ltl")){
		if(sat_solver == "nuxmv")
			satSolver = new NuxmvHandle(filename); 
		else
			satSolver = new SpotHandle(filename);
		domain = "ltl";
	}
	else{
		print_err("wrong input file");
		exit(1);
	}
	dimension = satSolver->dimension;	
	cout << "Dimension:" << dimension << endl;
        explorer = new Explorer(dimension);	
	explorer->satSolver = satSolver;
        verbose = false;
	depthMUS = 0;
	extend_top_variant = 0;
	dim_reduction = 0.5;
	output_file = "";
	validate_mus_c = false;
	hsd = false;
	hsd_succ = 0;
	verify_approx = false;
	total_difference_of_approximated_muses = 0;
	overapproximated_muses = rightly_approximated_muses = 0;
	current_depth = 0;
	explored_extensions = 0;
	spurious_muses = 0;
	skipped_shrinks = 0;
	unex_sat = unex_unsat = known_unex_unsat = extracted_unex = 0;
	rotated_muses = 0;
	duplicated = 0;
	max_round = 0;
	explicit_seeds = 0;

	if(domain == "sat"){
		int digits = 10;
		int pom = dimension;
		while(pom > 10){
			digits *= 10;
			pom /= 10;
		}
		cout << pom << endl;
	}
	use_edge_muses = true;
	rot_muses.resize(dimension, unordered_map<int, vector<int>>());
}

Solver::~Solver(){
	delete satSolver;
	delete explorer;
}

void Solver::write_mus_to_file(MUS& f){
	if(satSolver->clauses_string.size() != dimension){
		print_err("clauses_string err");
		return;
	}
	ofstream outfile;
	outfile.open(output_file, std::ios_base::app);
	for(auto c: f.int_mus)
		outfile << satSolver->clauses_string[c] << endl;
	outfile << endl;
	outfile.close(); 
}

// mark formula and all of its supersets as explored
void Solver::block_up(MUS& formula){
	explorer->block_up(formula);
}

// mark formula and all of its subsets as explored
void Solver::block_down(Formula formula){
        explorer->block_down(formula);
}

// experimental function
// allows output overapproximated MUSes 
bool Solver::check_mus_via_hsd(Formula &f){
	Formula bot = explorer->get_bot_unexplored(f);
	int size_bot = count_ones(bot);
	int size_f = count_ones(f);
	if(verbose) std::cout << "HSD: " << (size_f - size_bot) << ", hsd_succ: " << hsd_succ << endl << endl; 
	cout << "hsdd: " << (size_f - size_bot) << endl;
	bool result =  false;

	if(bot == f){
		result = true;
		cout << "guessed MUS" << endl;
	}

	else if((size_f - size_bot) < (dimension * mus_approx)){
		result = true;
		cout << "approximated MUS" << endl;
	}

	if(result){
		hsd_succ++;
		if(verify_approx){		
			Formula mus = satSolver->shrink(f);
			int f_size = count_ones(f);
			int mus_size = count_ones(mus);
			int distance = (f_size - mus_size);
			if(distance == 0){
				rightly_approximated_muses++;
				cout << "MUS approximation: success" << endl;				
			}
			else{
				overapproximated_muses++;
				total_difference_of_approximated_muses += distance;	
				cout << "MUS approximation: overapproximated, difference in size (over real MUS): " << distance << endl;
			}

			if(verbose){
				cout << "Total number of approximations: " << (rightly_approximated_muses + overapproximated_muses) << endl;
				cout << "Right approximations: " << rightly_approximated_muses << endl;
				cout << "Overapproximations: " << overapproximated_muses << endl;
				if(overapproximated_muses > 0){
					cout << "ratio right approximations / overapproximations: " << (rightly_approximated_muses / (float) overapproximated_muses) << endl;
					cout << "Average diff of overapproximation: " << (total_difference_of_approximated_muses / (float) overapproximated_muses) << endl;
				}	
			}
		}
	}
	return result;	
}

// check formula for satisfiability
// core and grow controls optional extraction of unsat core and model extension (replaces formula)
bool Solver::is_valid(Formula &formula, bool core, bool grow){
	bool result = satSolver->solve(formula, core, grow);

	if(model_rotation && result && count_zeros(formula) == 1){
		Formula model = satSolver->get_model();
		int critical;
		for(int i = 0; i < dimension; i++) 
			if(!formula[i]) 
				{ critical = i; break; }

		vector<int> new_criticals;
		int rotated = satSolver->critical_rotation(explorer->critical, critical, model, new_criticals);
//		cout << "ROTATED: " << rotated << endl;
		Formula whole(dimension, true);
		for(auto &crit: new_criticals){
			whole[crit] = false;
//			if(!satSolver->solve(whole,false,false)){ cout << "unsat..." << endl; exit(0); }
//			if(!explorer->checkValuation(whole)){ cout << "explored..." << endl; exit(0); }
			block_down(whole);
			whole[crit] = true;
		}					
	}

	return result;
}

//verify if f is a MUS
bool Solver::validate_mus(Formula &f){
//	cout << "mus size: " << count_ones(f) << endl;
	if(is_valid(f)){
		print_err("the mus is SAT");
		exit(1);
	}
	if(!explorer->checkValuation(f)){
		print_err("this mus has been already explored");
		exit(1);
		duplicated++;
	}	
/*	for(int l = 0; l < f.size(); l++)
		if(f[l]){
			f[l] = false;
			if(!is_valid(f)){
				print_err("the mus has unsat subset");	
				satSolver->export_formula(f, "spurious_mus");
				exit(1);
				spurious_muses++;				
				return false;
			}
			f[l] = true;
		}	
*/	if(verbose)
		cout << "validated" << endl;
	return true;
}

MUS& Solver::shrink_formula(Formula &f, Formula crits){
	//if(is_valid(f)) { cout << "shrinking valid formula"<< endl; exit(0); }
	//if(!explorer->checkValuation(f)){ cout << "shrinking explored formula" << endl; exit(0); }
	int f_size = count_ones(f);
	chrono::high_resolution_clock::time_point start_time = chrono::high_resolution_clock::now();
	if(crits.empty()) crits = explorer->critical;
	if(get_implies){	
		cout << "getting implies" << endl;
		explorer->get_implies(crits, f);		
		float ones_crits = count_ones(crits);		 
		if(f_size == ones_crits){ 
			cout << "skipped" << endl; 
			skipped_shrinks++; 
			muses.push_back(MUS(f, -1, muses.size())); //-1 duration means skipped shrink
			return muses.back();
		}		
		vector<bool> crits_copy = crits;
		std::cout << "ratio: " << (ones_crits/f_size) << endl;
		if((ones_crits/f_size) > crits_treshold){
			if(!is_valid(crits_copy, false, false)){ 
				cout << "guessed" << endl;
				skipped_shrinks++; 
				muses.push_back(MUS(crits, -1, muses.size()));//-1 duration means skipped shrink
				return muses.back();
			}
			if(criticals_rotation) satSolver->criticals_rotation(crits, f);
		}
	}

	Formula mus = satSolver->shrink(f, crits);
	chrono::high_resolution_clock::time_point end_time = chrono::high_resolution_clock::now();
	auto duration = chrono::duration_cast<chrono::microseconds>( end_time - start_time ).count() / float(1000000);
	muses.push_back(MUS(mus, duration, muses.size()));
	return muses.back();
}

//grow formula into a MSS
Formula Solver::grow_formula(Formula &f){
	return satSolver->grow(f);
}


void Solver::mark_MUS(MUS& f, bool block_unex){	
	if(validate_mus_c) validate_mus(f.bool_mus);		
	explorer->block_up(f, block_unex); //TODO: send a MUS, not Formula

	chrono::high_resolution_clock::time_point now = chrono::high_resolution_clock::now();
	auto duration = chrono::duration_cast<chrono::microseconds>( now - initial_time ).count() / float(1000000);
        cout << "Found MUS #" << muses.size() <<  ", mus dimension: " << f.dimension;
	cout << ", checks: " << satSolver->checks << ", time: " << duration;
//	cout << ", sat rotated: " << explorer->sat_rotated;
	cout << ", unex sat: " << unex_sat << ", unex unsat: " << unex_unsat << ", criticals: " << explorer->criticals;
	cout << ", intersections: " << std::count(explorer->mus_intersection.begin(), explorer->mus_intersection.end(), true);
	cout << ", rotated MUSes: " << rotated_muses << ", explicit seeds: " << explicit_seeds;
	cout << ", union: " << std::count(explorer->mus_union.begin(), explorer->mus_union.end(), true) << ", dimension: " << dimension << endl;

	if(output_file != "")
		write_mus_to_file(f);
}

void Solver::find_all_muses_marco_base(){
//	explorer->rotation_solver = true;
	Formula top = explorer->get_unexplored(1, false);
	Formula original_top;
	bool found_unsat = false;
	bool mus_after_rot = false;
	int sat_streak = 0;	
	int till_symbolic_seed = 5;
	int till_symbolic_seed_max = 5;
	bool rotated_top = false;
	while(!top.empty()){			
		original_top = top;
		bool invalid = (rotated_top)? true : !is_valid(top, true, true);
		if(!invalid){	
			block_down(top);		
			found_unsat = false;
			unex_sat++;
			sat_streak++;
			till_symbolic_seed--;
//			cout << sat_streak << "-" << explorer->sat_rotated << " " << flush;
		}	
		else{
			if(!rotated_top) till_symbolic_seed_max = 5;
			till_symbolic_seed = till_symbolic_seed_max;
			cout << endl;
			sat_streak = 0; found_unsat = true; unex_unsat++; mus_after_rot = true; 
			MUS mus = shrink_formula(top);			
			mark_MUS(mus);
		}	
		top = explorer->get_unexplored(1, false);
		rotated_top = false;
	}
}

/*
void Solver::find_all_muses_marco_complement(){
	Formula top = explorer->get_unexplored(1, false);
	bool known = false;	
	while(!top.empty()){
		bool invalid = known || !is_valid(top, true, true);
		known = false;
		if(invalid){
			MUS mus = shrink_formula(top);
			mark_MUS(mus);
			top = explorer->get_co_unexplored();
			if(!top.empty()){
				rotated_muses++;
				known = true;
				continue;
			}
		}else{
			block_down(top);
		}
		top = explorer->get_unexplored(1, false);
	}
}*/

void Solver::find_all_muses_marco_complement(){
	Formula top = explorer->get_unexplored(1, false);
	while(!top.empty()){	

		bool invalid;
		if(explorer->rotate_co(top)){
			rotated_muses++;	
			invalid = true;
		}else{
			invalid = !is_valid(top, true, true);
		}	
		if(!invalid){	
			block_down(top);		
			unex_sat++;
		}	
		else{
			unex_unsat++;
			MUS mus = shrink_formula(top);			
			mark_MUS(mus);
		}	
		top = explorer->get_unexplored(1, false);
	}
}

/*
int recursive_rotation(Formula &top, MUS &m1){

	//find m2

	Formula seed;
	vector<int> available_constraints;
	for(int i = 0; i < dimension; i++)
		if(!m1.bool_mus[i] || !m2.bool_mus[i])
			available_constraints.push_back(i);

	//very inefficient, just a proof of concept implementation	
	vector<vector<int>> hitting_pairs (dimension, vector<int>());
	for(auto c1: available_constraints)
		for(auto c2: available_constraints)
			if(c1 != c2 && explorer->is_hitting_pair(c1,c2))
				hitting_pairs[c1].push_back(c2);

	vector<pair<MUS, int>> local_muses = { make_pair(m1, c1), make_pair(m2, c2) };
	Formula seed = seeds[0];
	while(explorer->checkValuation(seed)){
		MUS mus = shrink_formula(seed);
		mark_mus(mus);
		for(auto c: available_constraints){
			if(!mus.bool_mus[c]) continue;			
			for(auto &m: local_muses){
				if(explorer->is_hitting_pair(c, m.second) && !m.first.bool_mus[c] && !mus.bool_mus[m.second]){ //availabel hitting pair
					
				}
			}
		}

		local_muses.push_back(mus);
	}
}*/

void Solver::find_all_muses_marco_recursive_rotation(){
	int crit_candidate = 0;
	Formula top = explorer->get_unexplored(1, false);
	while(!top.empty()){			
		Formula original_top = top;
		bool invalid = !is_valid(top, true, true);
		if(!invalid){	
			block_down(top);		
			unex_sat++;
		}	
		else{
			unex_unsat++;
			MUS mus = shrink_formula(top);			
			mark_MUS(mus);
			int rot = (variant == 50)? recursive_rotation_init(mus, original_top) : recursive_rotation_delta(mus, original_top, 0);
			cout << "recursively rotated: " << rot << endl;
		}	
		bool crit_attempt = false;
		while(crit_candidate < dimension){
			if(explorer->mus_intersection[crit_candidate++]){
				top = Formula(dimension, true); top[crit_candidate-1] = false; crit_attempt = true; break;
			}
		}
		if(!crit_attempt)
			top = explorer->get_unexplored(1, false);
	}
	
}

std::vector<int> used_before;
int repetitions;

int Solver::recursive_rotation_init(MUS &m1, Formula top){
	if(!explorer->easy_to_shrink(m1)) return 0;

	used_before.resize(dimension, 0);
	repetitions = 0;

	vector<int> top_int;
	for(int i = 0; i < dimension; i++)
		if(!top[i]) top_int.push_back(i);

	vector<int> scope_indicator(muses.size(), 2); //0 - inside, 1 - in scope, 2 - out of scope
	int in_scope = 0;
	vector<vector<int>> scope(dimension, vector<int>());
	for(int mid = 0; mid < muses.size(); mid++){
		auto &mus = muses[mid];
		if(!explorer->easy_to_shrink(mus)) continue;
		int c2, counter = 0;
		for(auto c: top_int){
			if(mus.bool_mus[c]){ c2 = c; if(++counter > 1) break; }
		}
		if(counter == 1){
			scope[c2].push_back(mid);		
			scope_indicator[mid] = 1; // the mus is in scope
			in_scope++;
		}
	}	
	scope_indicator[muses.size() - 1] = 0; //the initial MUS is the only MUS inside top
	cout << "s----------cope size: " << in_scope << endl << endl << endl;

	vector<int> local_muses;		
	int depth = 0;
//	no_pair.clear();
	int rot;
	if(use_edge_muses)
		rot = recursive_rotation_gama(m1, top_int, depth, scope_indicator, muses.size() - 1);	
	else	
		rot = recursive_rotation(m1, top_int, local_muses, scope, depth, scope_indicator);	
	cout << "repetitions: " << repetitions << endl;
	return rot;
}

void Solver::update_rot_muses(int c1, int c2, int rot_id, vector<int>& scope_indicator){
	if(rot_muses[c1].find(c2) == rot_muses[c1].end())
		rot_muses[c1].insert({c2, vector<int>{-1, -1, 0} });

	auto &rmuses = rot_muses[c1].find(c2)->second;		
	if(rmuses[1] == rot_id)
		return;

	// add all c1-c2 rotation muses
	for(int mid = rmuses[0] + 1; mid < muses.size(); mid++){
		auto &mus = muses[mid];
		if(mus.bool_mus[c2] && !mus.bool_mus[c1])
			rmuses.push_back(mid);
	}

	// move the muses in the scope to the start
	int to_put = 3;
	for(int i = 3; i < rmuses.size(); i++){
		auto mid = rmuses[i];
		if(scope_indicator[mid] < 2){
			rmuses[i] = rmuses[to_put];
			rmuses[to_put] = mid;
			to_put++;
		}
	}
	rmuses[2] = to_put;
}

vector<int> Solver::minimal_hitting_set(vector<int> local_muses){
	vector<int> hs;
	for(auto mid: local_muses){
		auto &mus = muses[mid];
		bool hitten = false;
		for(auto c: hs){ if(mus.bool_mus[c]){ hitten = true; break; } }
		if(hitten) continue;	
		hs.push_back(mus.without_crits[0]);
	}	
	return hs;
}

struct OverlapHash{
	public:
		std::size_t operator()(vector<int> const& over) const{
			std::size_t ret = over.size();
			for(auto &c: over){
				ret ^= c + 0x9e3779b9 + (ret << 6) + (ret >> 2);
			}
			return ret;
		}
};

int Solver::recursive_rotation_delta(MUS &m1, Formula &top, int depth){
	if(!explorer->easy_to_shrink(m1)) return 0;
	int rotated = 0;

	vector<int> top_int;
	for(int i = 0; i < dimension; i++)
		if(!top[i]) top_int.push_back(i);

	vector<int> indicator(muses.size(), 0);
	for(auto c2: top_int){
		for(auto mid: explorer->parent_muses[c2]){//TOTO mozna se omezit jen na poslednich k musu, tady i nize samozrejme
			indicator[mid]++;
		}
	}

	vector<vector<int>> local_muses_overlaps;
	vector<int> local_muses_ids;
//	vector<vector<int>> overlaps;//TODO: use unordered_set instead of vector
	unordered_set<vector<int>, OverlapHash> overlaps;	
	vector<bool> already_used_mus(muses.size(), false);
	for(auto c1: m1.without_crits){
		vector<int> pairs;	
		for(auto c: top_int){
			if(explorer->is_hitting_pair(c, c1)){ pairs.push_back(c); }
		}		
		for(auto c2: pairs){
			for(auto mid: explorer->parent_muses[c2]){
				auto &m2 = muses[mid];
				if(m2.bool_mus[c1] || indicator[mid] != 1 || already_used_mus[mid]) continue;
				vector<int> m1_overlap;
				for(auto o: m2.without_crits)
					if(o != c2 && !m1.bool_mus[o])
						m1_overlap.push_back(o);
				auto search = overlaps.find(m1_overlap);
				if(search != overlaps.end()) continue;
				overlaps.insert(m1_overlap);

				bool unexplored = true;
//				for(auto &overlap: local_muses_overlaps){					
				for(int i = 0; i < local_muses_overlaps.size(); i++){
					if(muses[local_muses_ids[i]].bool_mus[c1]) continue; //hitten by c1
					auto &overlap = local_muses_overlaps[i];
					bool hit = false;
					for(auto l: overlap){
						if(!m2.bool_mus[l] || l == c1){ //c1 cannot be in an overlap, fix it
							hit = true; break; 
						}
					}
					if(!hit){ unexplored = false; break; }
				}
				if(!unexplored) continue;
				Formula seed = m1.bool_mus; seed[c1] = false;
				for(auto o: m1_overlap) seed[o] = true;

				MUS m = shrink_formula(seed);
				mark_MUS(m);
				rotated++;
				rotated_muses++;
				already_used_mus[mid] = true;
				//local mus overlap
				vector<int> overlap;
				for(auto l: m.without_crits)
					if(!m1.bool_mus[l])
						overlap.push_back(l);
				local_muses_overlaps.push_back(overlap);
				local_muses_ids.push_back(muses.size() - 1);
			}
		}		
	}
	cout << "overlaps: " << overlaps.size() << endl;
	return rotated;
}

int Solver::recursive_rotation_gama(MUS &m1, vector<int> &top_int, int &depth, vector<int>& scope_indicator, int rot_id){
	if(!explorer->easy_to_shrink(m1)) return 0;
	vector<int> local_muses;
	vector<vector<int>> local_muses_overlaps;
	depth++;
	int rec_rotated = 0;
	int total = 0, used = 0;
	vector<vector<int>> used_before;
	int used_before_counter = 0;
	for(auto c1: m1.without_crits){
		if(explorer->mus_intersection[c1]) continue;
		vector<int> pairs;	
		for(auto c: top_int){
			if(explorer->is_hitting_pair(c, c1)){ pairs.push_back(c); }
		}		
		for(auto c2: pairs){
			update_rot_muses(c1, c2, rot_id, scope_indicator);
			auto &rmuses = rot_muses[c1].find(c2)->second;
			for(int i = 3; i < rmuses[2]; i++){
				total++;
				auto &m2 = muses[rmuses[i]];
				bool unexplored = true;
				int this_checks = 0;

				for(auto &overlap: local_muses_overlaps){					
					bool notsupset = false;
					for(auto l: overlap){
						this_checks++;						
						if(!m2.bool_mus[l] || l == c1){ 
							notsupset = true; break; 
						}
					}
					if(!notsupset){ unexplored = false; break; }
				}
				if(!unexplored) continue;
				Formula seed = union_sets(m2.bool_mus, m1.without_crits); seed[c1] = seed[c2] = false;
				float outof = count_ones(seed) * local_muses_overlaps.size() + 1;
				cout << "this checks: " << this_checks << " of " << outof << " " << (float(this_checks) / outof) << endl;
				MUS m = shrink_formula(seed);
				mark_MUS(m);

				//local mus overlap
				vector<int> overlap;
				for(auto l: m.without_crits)
					if(!m1.bool_mus[l])
						overlap.push_back(l);
				local_muses_overlaps.push_back(overlap);
				local_muses.push_back(muses.size() - 1);

				scope_indicator.push_back(0);// the new mus has no overlap with top
				rotated_muses++;	
				used++;			
				//break;
			}
		}		
	}
	if(total > 0){
		cout << used << " out of " << total << "  " << (float(used)/(total)) << ", depth: " << depth << endl;
		cout << "used before: " << used_before_counter << " " << (float(used_before_counter)/(total)) << endl;					
	}
	//try to find a seed for recursion
	if(false && !local_muses.empty()){
		local_muses.push_back(rot_id);
		auto hs = minimal_hitting_set(local_muses);
		Formula seed(dimension, true);
		for(auto c: hs) top_int.push_back(c);
		for(auto c: top_int) seed[c] = false;
		if(is_valid(seed, true, true)){
			block_down(seed);
		}
		else{
			MUS mus = shrink_formula(seed);			
			mark_MUS(mus);			
			scope_indicator.push_back(0);
			//update scope indicator
			for(int mid = 0; mid < muses.size(); mid++){
				auto &m = muses[mid];
				for(auto c: hs){
					if(m.bool_mus[c]) scope_indicator[mid]++;
				}
			}			
			rec_rotated += recursive_rotation_gama(mus, top_int, depth, scope_indicator, muses.size() - 1);
		}
	}

	depth--;
	return rec_rotated;
}

int Solver::recursive_rotation(MUS &m1, vector<int> &top_int, vector<int> &local_muses, vector<vector<int>> &scope, int &depth, vector<int>& scope_indicator){
	depth++;
	cout << "depth: " << depth << endl;
//	cout << "local muses: " << count_if(local_muses.begin(), local_muses.end(), [](int i){return scope_indicator[i] == 0;}) << " of " << local_muses.size() <<  endl;
	int rec_rotated = 0;
	int total = 0, used = 0;
	for(auto c1: m1.without_crits){ 
		if(explorer->mus_intersection[c1]) continue;
		used_before[c1]++;
		vector<int> pairs;	
		for(auto c: top_int){
			if(explorer->is_hitting_pair(c, c1)){ pairs.push_back(c); }
		}		
		for(auto c2: pairs){
			int c2_used = 0;
//			if(c2 < c1 && no_pair.find(key(c2,c1)) != no_pair.end()) continue;
//			if(c2 > c1 && no_pair.find(key(c1,c2)) != no_pair.end()) continue;
			for(auto mid: scope[c2]){
				total++;
				auto &m2 = muses[mid];

				if(m2.bool_mus[c1] && used_before[c1] > 1) repetitions++;

				if(m2.bool_mus[c1] || scope_indicator[mid] != 1) continue;
				Formula seed = union_sets(m2.bool_mus, m1.without_crits); seed[c1] = seed[c2] = false;
				//check if seed is unexplored
				bool unexplored = true;
				for(auto &mid: local_muses){ 
					if(scope_indicator[mid] > 0) continue; //excluded (already hitten by the stack)
					MUS &m = muses[mid];
					if(is_subset2(m.int_mus, seed)){
						unexplored = false; break;
					}
				}
				if(!unexplored) continue;
				c2_used++;
				MUS m = shrink_formula(seed);
				mark_MUS(m);
				local_muses.push_back(muses.size() - 1);
				scope_indicator.push_back(0);// the new mus has no overlap with top

				//update top
				top_int.push_back(c1);

				//update scope_indicator
				for(auto &pmid: explorer->parent_muses[c1])
					scope_indicator[pmid]++;

				rec_rotated += 1 + recursive_rotation(m, top_int, local_muses, scope, depth, scope_indicator);
				top_int.pop_back();

				//update scope_indicator
				for(auto &pmid: explorer->parent_muses[c1])
					scope_indicator[pmid]--;


				rotated_muses++;	
				used++;			
			}
//			if(c2_used == 0){
//				if(c2 < c1) no_pair[key(c2, c1)] = 0; //TODO: instead of inserting 0 insert e.g. id of the rotation call
//				else no_pair[key(c1, c2)] = 0;
//			}
		}		
	}
	if(total > 0)
		cout << used << " out of " << total << "  " << (float(used)/(total)) << endl;
	depth--;
	return rec_rotated;
}


/*
int Solver::recursive_rotation(MUS &m1, Formula top, vector<int> &local_muses){
	int rec_rotated = 0;
	int used_seeds = 0;
	int out_of_scope = 0;
	int attempts = 0;
	vector<int> top_int;
	for(int i = 0; i < dimension; i++)
		if(!top[i]) top_int.push_back(i);
	for(auto c1: m1.without_crits){ //TODO: we can restrict ourself to just local crits or even better to the top \setminus (union of scope muses)
		//TODO: here we can check if c1 was used above, i.e. directly by one of its parents on the stack. If yes, than perhaps we might continue
		if(explorer->mus_intersection[c1]) continue;
		Formula pairs(dimension, false);
		bool pair_found = false;
		for(auto c: top_int){
			if(explorer->is_hitting_pair(c, c1)){ pair_found = true; pairs[c] = true; }
		}
		if(!pair_found) continue; 
		//TODO: we can restrict ourself to scope MUSes
		int limit = muses.size(); //if we set the limit in the for cycle, i.e., i < muses.size(), then we will assume also the muses aded in recursion, which is useless 
		for(int i = 0; i < limit; i++){
			auto &mus = muses[i];
			if(mus.bool_mus[c1]) continue;
			int c2, counter = 0;
			for(auto c: top_int){
				if(mus.bool_mus[c]){ c2 = c; if(++counter > 1) break; }
			}
			attempts++;
			if(counter > 1) out_of_scope++;
			if(counter != 1 || !pairs[c2]) continue;
			Formula seed = union_sets(mus.bool_mus, m1.without_crits); seed[c1] = seed[c2] = false;
			//check if seed is unexplored
			bool unexplored = true;
			for(auto &mid: local_muses){ //TODO: no need to check muses that are gray, i.e. on the stack
				MUS &m = muses[mid];
				if(is_subset2(m.int_mus, seed)){
					unexplored = false; break;
				}
			}
			if(!unexplored) continue;
			MUS m = shrink_formula(seed);
			mark_MUS(m);
			local_muses.push_back(muses.size() - 1);
			top[c1] = false;
			rec_rotated += 1 + recursive_rotation(m, top, local_muses);
			top[c1] = true;
			used_seeds++;
			rotated_muses++;
		}
	}

	cout << "used seeds: " << used_seeds << endl;
	cout << "out of scope: " << out_of_scope << ", total: " << attempts << ", " << (float(out_of_scope) / attempts ) << endl;
	return rec_rotated;
}*/


/*int Solver::recursive_rotation(MUS &m1, Formula top, vector<int> &local_muses){
	auto seeds = explorer->init_rotation(top, m1);
	int rec_rotated = 0;
	int used_seeds = 0;
	for(pair<Formula, int> &seed: seeds){
		//check if seed is unexplored
		bool unexplored = true;
		for(auto &mid: local_muses){
			MUS &m = muses[mid];
			if(is_subset2(m.int_mus, seed.first)){
				unexplored = false; break;
			}
		}
		if(!unexplored) continue;
		MUS mus = shrink_formula(seed.first);
		mark_MUS(mus);
		local_muses.push_back(muses.size() - 1);
		top[seed.second] = false;
		rec_rotated += 1 + recursive_rotation(mus, top, local_muses);
		top[seed.second] = true;
		used_seeds++;
		rotated_muses++;	
	}
	cout << "used seeds: " << used_seeds << " of ouf " << seeds.size() << endl;
	return rec_rotated;
}*/


void Solver::find_all_muses_marco_explicit(){
	explorer->seed_priority_queue = true;
//	explorer->rotation_solver = true;
	Formula seed, original_seed;
	while(true){
		bool rotated = false;
		if(explorer->seed_priority_queue){
			seed = explorer->get_seed_explicit();
			if(!seed.empty()){
				rotated = true;
				explicit_seeds++;
				//cout << "explicit" << endl;
			}
		}
		if(!rotated){
			seed = explorer->get_unexplored(1, false);
			original_seed = seed;
			if(seed.empty()) return; //enumeration completed			
		}
		bool invalid = (rotated)? true : !is_valid(seed, true, true); 
		if(invalid){
			unex_unsat++;
			MUS mus = shrink_formula(seed);			
			Formula cover_top;
			if(explorer->test_rotation_unex){
				cover_top = (!rotated)? original_seed : explorer->get_top_unexplored(seed);
			}
			mark_MUS(mus);
			if(explorer->test_rotation_unex && explorer->easy_to_shrink(mus)){
				int rotated = mus_rotation(cover_top, mus);
				cout << "Rotated MUSes: " << rotated << endl;
			}
		}	
		else{
			//cout << "valid" << endl;
			unex_sat++;
//			Formula model = satSolver->get_model();
//			int rotation_limit = 100;
//			int sat_rotated = explorer->sat_rotation(original_seed, model, satSolver->clauses, rotation_limit);
//			cout << "sat rotated: " << sat_rotated << endl;
			block_down(seed);
		}				
	}
}



std::vector<bool> union_sets2(std::vector<bool> a, std::vector<bool> b){
	int dimension = a.size();
	std::vector<bool> res(dimension, false);
	for(int i = 0; i < dimension; i++)
		if(a[i] || b[i])	res[i] = true;
	return res;
}

//bool check_subset_int(std::vector<int> a, std::vector<int> b){
//
//}

int Solver::mus_rotation(Formula &top, MUS& mus){ //top = Top_2, mus = M_2
	vector<MUS> to_block;
	int c;
	int counter = 0;
	std::vector<std::pair<std::vector<bool>, int>> seeds = explorer->init_rotation(top, mus);
	int r = 0;
	for(auto &seed_pair: seeds){
		auto &seed = seed_pair.first;
		c = seed_pair.second;

		//check that the seed is still unexplored -- if c is in every previously found MUS then seed is unexplored
		//this check is too restrictive, we should check if none of the previously found MUSes is a subest of the seed
		bool unexplored = true;
		for(int i = 1; i < counter + 1; i++){
			auto &prev_mus = muses[muses.size() - i];
			if(is_subset2(prev_mus.without_crits, seed)){ unexplored = false; break; }//TODO: instead prev_mus.int_mus use prev_mus.without_crits			
		}
		if(unexplored){
			bool rotated = true;				
			while(rotated){
				counter++;
				rotated_muses++;
				rotated = false;
				MUS new_mus = shrink_formula(seed);
				mark_MUS(new_mus, false); //dont block yet
				to_block.push_back(new_mus); //block later (at the end of the function)
				break;//there is something not working, we are getting explored MUSes	
				int new_c = -1;	
				for(auto &i: new_mus.int_mus){
					if(!mus.bool_mus[i] && explorer->is_hitting_pair(c, i)){ new_c = i; break; }				
				}
				if(new_c != -1){
					seed = union_sets2(mus.bool_mus,new_mus.bool_mus);
					seed[c] = seed[new_c] = false;
					c = new_c;
					mus = new_mus;
					rotated = true;
				}				
			}	
		}
		if(!explorer->use_implications) break; 
	}

	cout << "rotation seeds: " << seeds.size() << ", rotated: " << counter << endl;
	if(!to_block.empty()){
		for(int i = 0; i < to_block.size() - 1; i++)
			explorer->block_up_unex(to_block[i].without_crits);
		MUS &last_mus = to_block[to_block.size() - 1];
		Formula new_top = explorer->get_top_unexplored(last_mus.bool_mus);
		explorer->block_up_unex(last_mus.without_crits);
		if(!new_top.empty()){
			counter += mus_rotation(new_top, last_mus);
		}
	}
	
	if(counter > max_round) max_round = counter;
	return counter;
}



void Solver::find_all_muses_daa(){
/*	Formula bot = explorer->get_unexplored(0, false);
	while(!bot.empty()){			
		if(is_valid(bot, true, true)){		
			Formula top = grow_formula(bot);
			block_down(top);		
		}	
		else{
			mark_MUS(bot);
		}		
		bot = explorer->get_unexplored(0, false);
	}*/
}

//remus
void Solver::find_all_muses_duality_based_remus(Formula subset, Formula crits, int depth){
	current_depth++;	
	std::vector<int> assumptions;
	for(int i = 0; i < dimension; i++){
		if(!subset[i]){
			assumptions.push_back(-1 * i - 1);			
		}
		//if(crits[i])	assumptions.push_back(i + 1); 
	}

	Formula top;	
	int streak = 0;	
	int iteration = 0;	
	bool top_found = false;
	while(true){
		iteration++;
		current_dimension = count_ones(subset);
		if(!top_found) top = explorer->get_top_unexplored(assumptions);
		top_found = false;
		if(top.empty())	{ 
			current_depth--; 
			return;
		}
		Formula origin_top = top;		
		if(!is_valid(top, true, true)){
			streak = 0;
			MUS mus = shrink_formula(top, crits);
			Formula rotation_top;
			if(explorer->test_rotation_unex){ rotation_top = explorer->get_top_unexplored(mus.bool_mus); }
			mark_MUS(mus);
			if(explorer->test_rotation_unex){ mus_rotation(rotation_top, mus); }

			if(depth > depthMUS) continue;
			Formula m = mus.bool_mus;
			extend_mus(origin_top, m);
			find_all_muses_duality_based_remus(m, crits, depth + 1);
		}
		else{	//top is necessarily an MSS of subset
			streak++;
			vector<bool> model;
			if(model_rotation){
				model = satSolver->get_model();
			}
			block_down(top);	
			if(variant == 10 && (streak > 2 || iteration == 1) && depth > 0){ current_depth--; return; }		
			vector<int> crit_all;
			for(int i = 0; i < dimension; i++)
				if(subset[i] && !origin_top[i]){
					crit_all.push_back(i);
				}
			if(crit_all.size() == 1){
				crits[crit_all[0]] = true;
				if(model_rotation){
					vector<vector<bool>> model_extensions;
					int rotated = satSolver->model_rotation(crits, crit_all[0], subset, model, model_extensions);
					for(auto &extension: model_extensions){
						if(false && !explorer->checkValuation(extension)) explored_extensions++;
						else block_down(extension);
					}					
				}
				continue;
			}	
			if(depth > depthMUS) continue;		
			for(auto crit: crit_all){
				Formula rec_subset = origin_top; //zde byl puvodne (omylem) top a ne origin_top, takze se neslo do rekurze. S top je to ale zajimava varianta
				rec_subset[crit] = true;

				Formula rec_crits = crits;
				rec_crits[crit] = true;
				if(model_rotation){			
					vector<vector<bool>> model_extensions;
					for(auto &extension: model_extensions){
						if(false && !explorer->checkValuation(extension)) explored_extensions++;
						else block_down(extension);
					}
				}

				find_all_muses_duality_based_remus(rec_subset, rec_crits, depth + 1);
			}
		}
	}
	current_depth--;
//	if(model_rotation) block_down(subset);
}

void Solver::find_all_muses_duality_based_mono_remus(Formula subset, Formula crits, int depth){
	current_depth++;	
	std::vector<int> assumptions;
	for(int i = 0; i < dimension; i++){
		if(!subset[i]){
			assumptions.push_back(-1 * i - 1);			
		}
		//if(crits[i])	assumptions.push_back(i + 1); 
	}

	Formula top;			
	while(true){
		//cout << "criticals: " << count_ones(crits) << ", subset dim: " << count_ones(subset) << endl;
		current_dimension = count_ones(subset);
		top = explorer->get_top_unexplored(assumptions);
		if(top.empty())	{ 
			current_depth--; 
			//if(model_rotation) block_down(subset); //not needed if model extension during model rotation is applied
			return;
		}
		Formula origin_top = top;		
		if(!is_valid(top, true, true)){
			MUS mus = shrink_formula(top, crits);
			mark_MUS(mus);
			//extend mus
			if(depth > depthMUS) continue;
			Formula m = mus.bool_mus;
			extend_mus(origin_top, m);
			find_all_muses_duality_based_mono_remus(m, crits, depth + 1);
		}
		else{	//top is necessarily an MSS of subset
			vector<bool> model;
			if(model_rotation){
				model = satSolver->get_model();
			}
			block_down(top);			
			vector<int> crit_all;
			for(int i = 0; i < dimension; i++)
				if(subset[i] && !origin_top[i]){
					crit_all.push_back(i);
				}
			//std::cout<< "mcs size: " << crit_all.size() << std::endl;
			if(crit_all.size() == 1){
				crits[crit_all[0]] = true;
				if(model_rotation){
					vector<vector<bool>> model_extensions;
					int rotated = satSolver->model_rotation(crits, crit_all[0], subset, model, model_extensions);
					for(auto &extension: model_extensions){
						if(false && !explorer->checkValuation(extension)) explored_extensions++;
						else block_down(extension);
					}					
				}
				continue;
			}	
		}
	}
	current_depth--;
	if(model_rotation) block_down(subset);
}




// Helper function for the TOME algorithm
pair<Formula, Formula> Solver::local_mus(Formula bot, Formula top, int diff){
	if(diff == 1)
		return make_pair(bot, top);
	int ones = 0;
	Formula pivot = bot;
	for(int i = 0; i < dimension; i++)
		if(!pivot[i] && top[i]){
			pivot[i] = true;
			if(++ones >= diff/2)
				break;
		}
	if(is_valid(pivot))
		return local_mus(pivot, top, diff - ones);	
	else
		return local_mus(bot, pivot, ones);
}

// The core of the TOME algorithm for MUS enumeration
void Solver::find_all_muses_tome(){
/*	Formula bot, top, mus, mss;
	vector<Formula> path;
	int diff;
	while(true){
		bot = explorer->get_unexplored(0, false);
		if(bot.empty()) break;
		top = explorer->get_top_unexplored(bot);
		if(is_valid(top)){
			block_down(top);
			continue;
		}
		if(!is_valid(bot)){
			mark_MUS(bot);
			continue;
		}	
		diff =  std::count(top.begin(), top.end(), true) - std::count(bot.begin(), bot.end(), true);
		auto locals = local_mus(bot, top, diff);
		mus = locals.second;
		mss = locals.first;
		mark_MUS(shrink_formula(mus));
		block_down(mss);
	}*/
}
	

// helper funcion for the ReMUS algorithm (experimental, not integrated yet)
// modifies mus into a set S such that mus /subseteq S /subseteq top
void Solver::extend_mus(Formula &top, Formula &mus, int dMUS){
	switch (extend_top_variant) {
		case 1:
			int origin_top_size = count_ones(top);
			int ones = count_ones(mus);
			for(int i = 0; i < dimension; i++)
				if(top[i] && !mus[i]){
					mus[i] = true;
					ones++;
					if(ones >= origin_top_size * dim_reduction) 
						break;
				}			
			break;
	}	
}

void Solver::enumerate(){
	initial_time = chrono::high_resolution_clock::now();
	cout << "running algorithm variant " << variant << endl;
	Formula whole(dimension, true);
	if(is_valid(whole)){
		cout << "the input instance is satisfiable" << endl;
		exit(1);
	}

	switch (variant) {
		case 1:
		case 10:
			find_all_muses_duality_based_remus(Formula (dimension, true), Formula (dimension, false), 0);
			break;						
		case 2:
			find_all_muses_tome();
			break;
		case 30:
			find_all_muses_marco_base();
			break;
		case 35:
			find_all_muses_marco_explicit();
			break;
		case 40:
			find_all_muses_marco_complement();
			break;
		case 50:
		case 55:
			find_all_muses_marco_recursive_rotation();
			break;
		case 4:
			find_all_muses_duality_based_mono_remus(Formula (dimension, true), Formula (dimension, false), 0);
			break;
		case 5:
			find_all_muses_daa();
			break;
		default:
			print_err("invalid algorithm chosen");
			break;
	}
	return;
}

