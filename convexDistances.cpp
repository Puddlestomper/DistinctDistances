#include <vector>
#include <array>
#include <queue>
#include <unordered_set>
#include <stdio.h>
#include <string>
#include <time.h>
#include <cassert>

/*
TODO:
1. Apply Lemmas - bisector
2. Apply Lemmas - quad
*/

#define N 9
#define K 5

constexpr int totalNodes = K + N * (N-1) / 2;

struct Node
{
	int index;
	int dist, upBound, lowBound; // upBound and lowBound are equality inclusive
	int a, b;
	std::unordered_set<int> edges, in_edges; // edges are those less than it and in_edges are those larger than it

	Node(int index)
		: index(index), dist(-1), upBound(0), lowBound(K-1), edges(), in_edges() {}
};

struct ConvexDistanceGraph
{
	std::vector<Node> nodes;
	std::vector<int> known_nodes[K]; // Will include fixed distance nodes
	std::array<std::array<int, N>, N> lookup;
	bool change = false;

	// Caching
	std::array<std::array<bool, N>, N> perpBisecSolved;

	ConvexDistanceGraph()
	{
		// Create all the nodes
		nodes.reserve(K + N * (N-1) / 2);

		for(int i = 0; i < K; i++)
		{
			nodes.emplace_back(-1-i); // Index 0 to K-1 is d_1 to d_k
		}

		int ind = K;
		for(int i = 0; i < N - 1; i++) for(int j = i + 1; j < N; j++)
		{
			lookup[i][j] = ind;
			lookup[j][i] = ind;
			nodes.emplace_back(ind++);
			nodes.back().a = i;
			nodes.back().b = j;
		}

		if(nodes.size() != totalNodes) printf("[ERROR] Wrong node amount!\n");

		// Set relationship between d_1 to d_K
		for(int i = 0; i < K - 1; i++) for(int j = i + 1; j < K; j++)
		{
			addEdge(j, i);
		}
		for(int i = 0; i < K; i++)
		{
			nodes[i].dist = i;
			known_nodes[i].push_back(i);
		}

		// Caching init

		for(int i = 0; i < N; i++) perpBisecSolved[i].fill(false);
	}

	void setD1Nodes(const std::vector<int>& new_nodes, bool noOtherD1Nodes = false)
	{
		// printf("[PRELOOP] Doing d1 nodes\n");

		known_nodes[0].insert(known_nodes[0].end(), new_nodes.begin(), new_nodes.end()); // Append these distances to the list of d1 nodes
		
		for(int i : new_nodes) nodes[i].dist = 0;

		if(noOtherD1Nodes) for(int i = 1; i < totalNodes; i++) if(nodes[i].dist != 0) // Everything else is less than d1
		{
			addEdge(i, 0);
			for(int j : new_nodes) addEdge(i,j);
		}
	}

	// Applies all calculations until no more change
	void resolve()
	{
		do
		{
			for(int i = K; i < totalNodes; i++)
			{
				setLowerBound(i, K-1);
				setUpperBound(i, 0);
			}
			
			// printf("[LOOP] Here we go again\n");
			change = false;

			applyBisectorLemma();
			applyQuadLemma();

			// printf("[LOOP] Lemmas applied\n");

			updateLowerBounds(); // If d_5 < a < b, then d_4 < b

			// printf("[LOOP] Lower bounds done\n");

			resolveDistances(); // Look for chains of inequalities and update them. Also look for partial chains to upper bound distances

			// printf("[LOOP] Distances resolved\n");
		} while (change);

		for(int i = K; i < totalNodes; i++)
		{
			setLowerBound(i, K-1);
			setUpperBound(i, 0);
		}
	}

	void applyBisectorLemma()
	{
		// Must set change to true if adding an edge --- note the addEdge function does this for you.

		for(int i1 = 0; i1 < N; i1++) for(int i2 = 0; i2 < N - 1; i2++) for(int i3 = 0; i3 < N - 2 - i2; i3++)
		{
			int v1 = i1;
			int v2 = (v1 + 1 + i2) % N;
			int v3 = (v2 + 1 + i3) % N;

			if(perpBisecSolved[v2][v3]) continue;

			int e12 = lookup[v1][v2];
			int e13 = lookup[v1][v3];

			// printf("%.3i, %.3i\n", e12, e13);

			// 3 cases: edges equal, and two possible directions for inequalities

			bool left_flag = false, right_flag = false;

			if(nodes[e12].dist != -1 && nodes[e12].dist == nodes[e13].dist) // equal distances. In this case we are done with deducing for the v2v3 edge
			{
				left_flag = true;
				right_flag = true;

				perpBisecSolved[v2][v3] = true;
				perpBisecSolved[v3][v2] = true;
			}
			else if(nodes[e12].edges.count(e13) > 0 || nodes[e12].dist == 0) // e12 > e13 or e12 is max dist (ie e12 >= e13)
			{
				left_flag = true;
			}
			else if(nodes[e13].edges.count(e12) > 0 || nodes[e13].dist == 0) // e12 < e13 or e13 is max dist (ie e13 >= e12)
			{
				right_flag = true;
			}

			if(right_flag) for(int j = 0; j < i2; j++) // everything counter clockwise from e12
			{
				int vj = (v1 + 1 + j) % N;

				// printf("%.2i", vj);

				int e2j = lookup[vj][v2];
				int e3j = lookup[vj][v3];

				// printf(" \t|%.3i, %.3i\n", e2j, e3j);

				addEdge(e2j, e3j);
			}

			if(left_flag) for(int j = 0; j < N - 3 - i2 - i3; j++) // everything clockwise from e13
			{
				int vj = (v3 + 1 + j) % N;

				int e2j = lookup[vj][v2];
				int e3j = lookup[vj][v3];

				addEdge(e3j, e2j);
			}
		}
	}

	void applyQuadLemma()
	{
		// Must set change to true if adding an edge --- note the addEdge function does this for you.
	}

	// Find chains of K distances and set them
	// BFS starting at d_1 and we want the longest distance to each node
	void resolveDistances()
	{
		std::array<int, totalNodes> dists, parent;
		std::array<bool, totalNodes> visited;
		dists.fill(-1);
		parent.fill(-1);
		visited.fill(false);
		std::queue<int> q;

		// Manually process distance zero nodes
		for(int i : known_nodes[0])
		{
			dists[i] = 0;
			for(int j : nodes[i].edges)
			{
				parent[j] = i;
				q.push(j);
			}
			visited[i] = true;
		}

		// BFS
		runBFS(q, dists, parent, visited);

		// Also add everything which hasn't been visited - hopefully gives more upper bounds for nodes
		for(int i = K; i < totalNodes; i++) if(!visited[i] && nodes[i].edges.size() > 0)
		{
			dists[i] = 0;
			for(int j : nodes[i].edges) if(parent[j] == -1) // No need to visit this child again if it has been visited form another place
			{
				parent[j] = i;
				q.push(j);
			}

			visited[i] = true;
		}

		runBFS(q, dists, parent, visited);

		// Now check for nice chains

		for(int i = K; i < totalNodes; i++)
		{
			if(dists[i] == K-1)
			{
				chainFound(dists, i);
				
				// int node = i;
				// int dist = K-1;

				// for(int dist = K - 1; dist > 0; dist--)
				// {
				// 	if(dist != dists[node]) printf("[ERROR] Node %.1i being set to different dist from BFS: %.1i in BFS vs %.1i\n", node, dists[node], dist);
				// 	setDistance(node, dist);
				// 	node = parent[node];
				// }
				// if(dists[node] != 0) printf("[ERROR] Had chain of nodes but initial node (%.1i) was not dist 0\n", node);
			}
		}

		// We also know that the dist upper bounds the distance it could be

		for(int i = K; i < totalNodes; i++)
		{
			if(dists[i] > 0) addEdge(i, dists[i] - 1);
		}
	}

	void runBFS(std::queue<int>& q, std::array<int, totalNodes>& dists, std::array<int, totalNodes>& parent, std::array<bool, totalNodes>& visited)
	{
		while(!q.empty())
		{
			int ind = q.front();
			int parentDist = dists[parent[ind]];

			// printf("BFS at index %s with distance %.1i\n", toString(ind).c_str(), parentDist);

			if(dists[ind] < parentDist + 1)
			{
				dists[ind] = parentDist + 1;
				for(int i : nodes[ind].edges)
				{
					if(parent[i] == -1 || dists[ind] > dists[parent[i]])
					{
						parent[i] = ind;
						q.push(i);
					}
				}
			}

			visited[ind] = true;

			q.pop();
		}
	}

	void chainFound(const std::array<int, totalNodes>& dists, int endInd, int dist = K-1)
	{
		if(dist == 0) return;
		setDistance(endInd, dist);
		for(int i : nodes[endInd].in_edges)
		{
			if(dists[i] == dist - 1) chainFound(dists, i, dist - 1);
		}
	}

	void updateLowerBounds()
	{
		for(int k = K-1; k > 1; k--) for(int i : nodes[k].in_edges)
		{
			if(i < K) continue;
			for(int j : nodes[i].in_edges) addEdge(k-1, j);
		}
	}

	void setDistance(int index, int distInd)
	{
		if(index < K)
		{
			if(index != distInd) printf("[ERROR] Special edge (%1i) set to wrong distance: %1i!\n", index, distInd);
			return;
		}
		
		if(nodes[index].dist == -1)
		{
			// printf("Add distance %.1i to edge %s", distInd, toString(index).c_str());
			if(distInd == 0) printf("[INFO] Adding another largest distance at %s!\n", toString(index).c_str());

			// for(int i = 0; i < K; i++) // Add relations to fixed distances - should not need this because it should be covered below by transitivity
			// {
			// 	if(i < distInd) addEdge(index, i);
			// 	else if(i > distInd) addEdge(i, index);
			// }

			// Update relations to other known edges
			if(distInd > 0) for(int i : known_nodes[distInd - 1]) addEdge(index, i);
			if(distInd < K - 1) for(int i : known_nodes[distInd + 1]) addEdge(i, index);

			nodes[index].dist = distInd;
			nodes[index].upBound = distInd;
			nodes[index].lowBound = distInd;
			known_nodes[distInd].push_back(index);
			change = true;
		}
		else if(nodes[index].dist != distInd)
		{
			printf("[ERROR] Same edge (%s) set to two distances: %1i and %1i!\n", toString(index).c_str(), nodes[index].dist, distInd);
		}
	}

	void addEdge(int a, int b, bool addingFixed = false) // a < b
	{
		if(a == b) printf("[ERROR] Same distance less than itself\n");
		
		nodes[a].in_edges.insert(b);
		auto ans = nodes[b].edges.insert(a);

		change = change || ans.second;

		if(ans.second) // Transitivity if it actually adds a new edge
		{
			// if(a >= K && b >= K) printf("Added edge %s to %s with a=%.3i and b=%.3i\n", toString(a).c_str(), toString(b).c_str(), a, b);
			
			for(int i : nodes[a].edges) addEdge(i, b);
			for(int i : nodes[b].in_edges) addEdge(a, i);

			if(nodes[a].edges.count(b) > 0) printf("[ERROR] Edge %s and edge %s violate anti-symmetry!\n", toString(a).c_str(), toString(b).c_str());
		}

		if(ans.second && nodes[b].dist != -1 && nodes[a].dist == -1 && !addingFixed) // We know a is less than a fixed distance so it should also be less than everything else of that distance
		{
			int dist = nodes[b].dist;
			if(nodes[a].upBound < dist + 1) setUpperBound(a, dist + 1);
			for(int i : known_nodes[dist]) if(i != b) addEdge(a, i, true);
		}

		if(ans.second && nodes[a].dist != -1 && nodes[b].dist == -1 && !addingFixed) // We know b is more than a fixed distance so it should also be more than everything else of that distance
		{
			int dist = nodes[a].dist;
			if(nodes[b].lowBound > dist - 1) setLowerBound(b, dist - 1);
			for(int i : known_nodes[dist]) if(i != a) addEdge(i, b, true);
		}

	}

	void setLowerBound(int index, int bound)
	{
		if(bound < nodes[index].lowBound) nodes[index].lowBound = bound;

		for(int i : nodes[index].in_edges) if(nodes[i].lowBound > bound - 1) setLowerBound(i, bound - 1);
	}

	void setUpperBound(int index, int bound)
	{
		if(bound > nodes[index].upBound) nodes[index].upBound = bound;

		for(int i : nodes[index].edges) if(nodes[i].upBound < bound + 1) setUpperBound(i, bound + 1);
	}

	inline std::string toString(int nodeIndex) const
	{
		if(nodeIndex < K) return "d" + std::to_string(nodeIndex + 1);
		
		return "V" + std::to_string(nodes[nodeIndex].a + 1) + "-V" + std::to_string(nodes[nodeIndex].b + 1);
	}
};

void printKnownDistances(const ConvexDistanceGraph& cdg)
{
	printf("Distance Table:\n----------------------------------\n");
	
	printf(" d|");
	for(int i = 0; i < N; i++) printf("%2i|", i+1);
	printf("\n");
	for(int i = 0; i < N; i++)
	{
		printf("%2i|", i+1);	
		for(int j = 0; j < N; j++)
		{
			int e = cdg.lookup[i][j];
			if (i == j) printf("xx|");
			else if(cdg.nodes[e].dist != -1) printf("%2i|", cdg.nodes[e].dist + 1);
			else printf("  |");
		}
		printf("\n");
	}
	printf("----------------------------------\n");

	printf("Lower Bound Table:\n----------------------------------\n");
	
	printf(" L|");
	for(int i = 0; i < N; i++) printf("%2i|", i+1);
	printf("\n");
	for(int i = 0; i < N; i++)
	{
		printf("%2i|", i+1);	
		for(int j = 0; j < N; j++)
		{
			int e = cdg.lookup[i][j];
			if (i == j) printf("xx|");
			else if(cdg.nodes[e].dist != -1) printf("d%1i|", cdg.nodes[e].dist + 1);
			else if(cdg.nodes[e].lowBound < K-1) printf("%2i|", cdg.nodes[e].lowBound + 1);
			else printf("  |");
		}
		printf("\n");
	}
	printf("----------------------------------\n");

	printf("Upper Bound Table:\n----------------------------------\n");
	
	printf(" U|");
	for(int i = 0; i < N; i++) printf("%2i|", i+1);
	printf("\n");
	for(int i = 0; i < N; i++)
	{
		printf("%2i|", i+1);	
		for(int j = 0; j < N; j++)
		{
			int e = cdg.lookup[i][j];
			if (i == j) printf("xx|");
			else if(cdg.nodes[e].dist != -1) printf("d%1i|", cdg.nodes[e].dist + 1);
			else if(cdg.nodes[e].upBound > 0) printf("%2i|", cdg.nodes[e].upBound + 1);
			else printf("  |");
		}
		printf("\n");
	}
	printf("----------------------------------\n");
}

void printAlmostChains(const ConvexDistanceGraph& cdg)
{
	printf("Some long chains:\n----------------------------------\n");
	
	std::vector<int> chainEnds;

	for(int i = K; i < totalNodes; i++) if(cdg.nodes[i].dist == -1 && cdg.nodes[i].in_edges.count(K-3) > 0)
	{
		chainEnds.push_back(i);
	}

	for(int i : chainEnds) // print one chain for each
	{
		int dist = K-2;
		int target = i;

		while(dist > -1)
		{
			if(target == -1)
			{
				printf("[ERROR] Chain wonky\n"); // Should never happen
				break;
			}
			
			if(dist > 0) printf("%s < ", cdg.toString(target).c_str());
			else printf("%s\n", cdg.toString(target).c_str());
			int newtarget = -1;
			for(int j : cdg.nodes[target].in_edges)
			{
				if(newtarget == -1) newtarget = j;
				else if (newtarget < K && j >= K)
				{
					newtarget = j;
					break;
				}
			}

			target = newtarget;
			dist--;
		}
	}
	printf("----------------------------------\n");
}

void printEdgesKnown(const ConvexDistanceGraph& cdg)
{
	int totalLengths = (N) * (N-1) / 2;
	int totalEdges = (totalLengths + K) * (totalLengths + K - 1) / 2;

	int knownEdges = 0;
	for(int i = 0; i < totalNodes; i++) knownEdges += cdg.nodes[i].edges.size();

	printf("Known edges: %i / %i\n", knownEdges, totalEdges);
}

void fullPrint(const ConvexDistanceGraph& cdg)
{
	printf("----------------------------------\n");
	
	printKnownDistances(cdg);

	printAlmostChains(cdg);

	printEdgesKnown(cdg);
}


// 
// 
// 
// 
// 
//    BELOW IS STATE SETUP FOR CASES
// 
// 
// 
// 
// 
// 





void setMinD1Distance(ConvexDistanceGraph& cdg, int dist) // everything less than i to i+dist will be less than d1
{
	for(int i = 0; i < N; i++)
	{
		for(int j = 1; j < dist; j++)
		{
			int v2 = (i + j) % N;
			int e = cdg.lookup[i][v2];
			cdg.addEdge(e, 0);
		}
	}
}

void initialDistances_N9_Case3A(ConvexDistanceGraph& cdg)
{
	assert(N == 9 && K == 5);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 4}, {0, 5}, {1, 6}, {2, 6}, {3, 7}, {3, 8}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, true); // It is assumed that there are no other edges of length d1, I can change this if need be.
}

void initialDistances_N9_Case3B(ConvexDistanceGraph& cdg)
{
	assert(N == 9 && K == 5);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 4}, {0, 5}, {4, 8}, {2, 6}, {2, 7}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, false); 

	setMinD1Distance(cdg, 4); // Set minimum distance between nodes for a distance d1
}

void initialDistances_N11_Case3AI(ConvexDistanceGraph& cdg)
{
	assert(N == 11 && K == 6);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 5}, {0, 6}, {9, 3}, {9, 4}, {2, 7}, {2, 8}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, true); // True = It is assumed that there are no other edges of length d1
}

void initialDistances_N11_Case3AII(ConvexDistanceGraph& cdg)
{
	assert(N == 11 && K == 6);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 5}, {0, 6}, {9, 3}, {9, 4}, {1, 7}, {2, 7}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, true); // True = It is assumed that there are no other edges of length d1
}

void initialDistances_N11_Case3AIII(ConvexDistanceGraph& cdg)
{
	assert(N == 11 && K == 6);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 5}, {0, 6}, {3, 9}, {3, 8}, {1, 7}, {2, 7}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, true); // True = It is assumed that there are no other edges of length d1
}

void initialDistances_N11_Case3AIV(ConvexDistanceGraph& cdg)
{
	assert(N == 11 && K == 6);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 5}, {0, 6}, {4, 9}, {4, 10}, {1, 7}, {2, 7}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, true); // True = It is assumed that there are no other edges of length d1
}

void initialDistances_N11_Case3B(ConvexDistanceGraph& cdg)
{
	assert(N == 11 && K == 6);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 5}, {0, 6}, {5, 10}, {3, 8}, {3, 9}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, false);

	setMinD1Distance(cdg, 5);
}

void initialDistances_N11_Case3C(ConvexDistanceGraph& cdg)
{
	assert(N == 11 && K == 6);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 5}, {0, 6}, {5, 10}, {4, 10}, {4, 9}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, false);

	setMinD1Distance(cdg, 5);
}

void initialDistances_N11_Case3D(ConvexDistanceGraph& cdg)
{
	assert(N == 11 && K == 6);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 5}, {0, 6}, {5, 10}, {1, 7}, {2, 7}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, false);

	setMinD1Distance(cdg, 5);
}

void initialDistances_N11_Case3E(ConvexDistanceGraph& cdg)
{
	assert(N == 11 && K == 6);
	// Set everything which is d1, and any other necessary edge inequalities.
	std::vector<std::pair<int, int>> d1_pairs = {{0, 5}, {0, 6}, {5, 10}, {2, 8}, {3, 8}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs) d1_edges.push_back(cdg.lookup[p.first][p.second]);
	cdg.setD1Nodes(d1_edges, false);

	setMinD1Distance(cdg, 5);
}

void initialDistances_N11_test(ConvexDistanceGraph& cdg)
{
	assert(N == 11 && K == 6);
	
	std::vector<std::pair<int, int>> d1_pairs = {{0, 4}, {0, 5}, {4, 10}};
	std::vector<int> d1_edges;

	for(auto p : d1_pairs)
	{
		d1_edges.push_back(cdg.lookup[p.first][p.second]);
	}

	cdg.setD1Nodes(d1_edges, true);

	setMinD1Distance(cdg, 4);
}

void time_test()
{
	clock_t start = clock();
	
	for(int i = 0; i < 1000; i++)
	{
		ConvexDistanceGraph cdg = ConvexDistanceGraph();
	
		initialDistances_N9_Case3A(cdg);

		cdg.resolve();

		// printKnownDistances(cdg);
	}
	
	clock_t end = clock();

	printf("Time taken: %.3f seconds\n", (float)(end - start) / CLOCKS_PER_SEC);
}

int main()
{
	ConvexDistanceGraph cdg = ConvexDistanceGraph();
	
	initialDistances_N9_Case3A(cdg);
	// initialDistances_N11_Case3B(cdg);

	cdg.resolve();

	fullPrint(cdg);

	return 0;
}