#ifndef TYPES_H
#define TYPES_H

#include <vector>

typedef std::vector<bool> Formula;
typedef std::vector<int> Block;
typedef std::tuple<int, int, int, int, int> triple; //m1, m2, c1, c2, size

class MUS{
	public:
	MUS(Formula& f, float d, int idc){
		bool_mus = f;
		for(int i = 0; i < f.size(); i++)
			if(f[i])
				int_mus.push_back(i);
		without_crits = int_mus;		
		dimension = int_mus.size();
		duration = d;
		id = idc++;
	}
	Formula bool_mus;
	std::vector<int> int_mus;
	std::vector<int> without_crits;
	int dimension;
	float duration;
	int id;
};


#endif
