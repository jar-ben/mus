#include "MSHandle.h"
#include "Explorer.h"
#include "Z3Handle.h"
#include "SpotHandle.h"
#include "NuxmvHandle.h"
#include "types_h.h"
#include <set>
#include <list>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <utility>
#include <ctime>
#include <chrono>	
#include <unordered_map>

inline size_t key(int i, int j){ return (size_t) i << 32 | (unsigned int) j; }

using namespace std;

typedef vector<int> Clause;
typedef vector<Formula> Path;
typedef Path::iterator PathIter;

class Solver{
public:
	int dimension; //dimension of the input instance
	int variant; //MUS enumeration algorithm to be used
	int isValidExecutions;
	bool verbose; //TODO: make it int based 
	int depthMUS;
	int extend_top_variant;
	float dim_reduction;
	string output_file;
	bool hsd;
	int hsd_succ;
	int block_down_mus;
	bool validate_mus_c;
	float mus_approx;
	bool verify_approx;
	int overapproximated_muses;
	int rightly_approximated_muses;	
	int total_difference_of_approximated_muses;
	int current_depth;
	int current_dimension;
	bool model_rotation;
	int explored_extensions;
	int spurious_muses;
	bool get_implies;
	int skipped_shrinks;
	float crits_treshold;
	bool criticals_rotation;
	string domain;

	int unex_unsat;
	int unex_sat;
	int known_unex_unsat;
	int extracted_unex;

	chrono::high_resolution_clock::time_point initial_time;
	
	vector<MUS> muses;
	Explorer* explorer;
	SatSolver* satSolver; 
	string sat_solver;

	Solver(string filename, int var = 1, bool vis = false, string sat_solver = "");
	~Solver();
	bool is_valid(Formula &f, bool core = false, bool grow = false);
	void block_down(Formula f);
	void block_up(MUS& f);
	void mark_MUS(MUS& m, bool block = true);
	MUS& shrink_formula(Formula& f, Formula crits = Formula());
	Formula grow_formula(Formula& f);
	void write_mus_to_file(MUS& f);

	bool validate_mus(Formula &f);

	//reMUS algorithm functions
	void find_all_muses_duality_based_remus(Formula subset, Formula crits, int depth);
	void find_all_muses_duality_based_mono_remus(Formula subset, Formula crits, int depth);
	void extend_mus(Formula &top, Formula &mus, int dMUS = 1);

	//TOME algorithm functions
	void find_all_muses_tome();
	pair<Formula, Formula> local_mus(Formula bot, Formula top, int diff);

	//MARCO algorithm functions
	void find_all_muses_marco_base();
	void find_all_muses_marco_explicit();
	void find_all_muses_marco_complement();
	int explicit_seeds;

	void find_all_muses_marco_recursive_rotation();
	int recursive_rotation(MUS &m1, vector<int> &top_int, vector<int> &local_muses, vector<vector<int>> &scope, int &depth, vector<int> &scope_indicator);
	int recursive_rotation_init(MUS &m1, Formula top);
	bool use_edge_muses;


	void update_rot_muses(int c1, int c2, int rot_it, vector<int>& scope_indicator);
	int recursive_rotation_gama(MUS &m1, vector<int> &top_int, int &depth, vector<int>& scope_indicator, int rot_id);
	int recursive_rotation_delta(MUS &m1, Formula &top, int depth);
	vector<unordered_map<int, vector<int>>> rot_muses;
	vector<int> minimal_hitting_set(vector<int> local_muses);


	int mus_rotation(Formula &top, MUS& mus);
	int rotated_muses;
	int duplicated;
	int max_round;

	//DAA algorithm functions
	void find_all_muses_daa();

	bool check_mus_via_hsd(Formula &f);
	void enumerate();


};
