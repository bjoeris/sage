
import sage.all
import sage.graphs.all
from sage.graphs.all import graphs, EdgeLabelledGraph

from sage.graphs.graph_decompositions.spqr_tree_unrooted import SPQRTree

from hypothesis import given, example, settings, HealthCheck

from hypothesis.strategies import integers, composite, sampled_from, permutations

import unittest

@composite
def complete_graph_fundamental_cycles(draw):
    n = draw(integers(3,12))
    G = EdgeLabelledGraph(graphs.CompleteGraph(n))
    u = draw(sampled_from(G))
    found = {u}
    tree_edges = set()
    while len(found) < len(G):
        v = draw(sampled_from(G.neighbors(u)))
        if not v in found:
            found.add(v)
            e = G.edge_label(u, v)
            tree_edges.add((u, v, e))
        u = v
    tree_edge_labels = {e for _, _, e in tree_edges}
    def find_cycle(e):
        return [label for _,_,label in G.subgraph(edges=tree_edges | {e})
                  .is_forest(certificate=True,output='edge')[1]]
    cycles = [find_cycle(e) for e in G.edges() if e[2] not in tree_edge_labels]
    cycles = draw(permutations(cycles))
    return G, cycles

class TestSPQR(unittest.TestCase):
    @settings(suppress_health_check=[HealthCheck.too_slow])
    @given(complete_graph_fundamental_cycles())
    @example((EdgeLabelledGraph(graphs.CompleteGraph(6)),
              [[10, 1, 3],
               [12, 2, 3],
               [11, 10, 3, 4],
               [10, 5, 0, 3],
               [12, 6, 0, 3],
               [7, 0, 3],
               [10, 11, 8, 0, 3],
               [9, 10, 12],
               [13, 11, 10, 12],
               [11, 10, 14]]))
    @example((EdgeLabelledGraph(graphs.CompleteGraph(6)),
              [[9, 5, 0, 2],
               [9, 1, 2],
               [7, 5, 9, 2, 3],
               [5, 6, 9],
               [8, 5, 9, 2, 4],
               [7, 5, 10],
               [11, 9, 2, 4],
               [7, 5, 9, 12],
               [13, 2, 4],
               [14, 7, 5, 9, 2, 4]]))
    @example((EdgeLabelledGraph(graphs.CompleteGraph(5)),
              [[9, 8, 1, 2],
               [8, 1, 3],
               [4, 0, 1],
               [8, 9, 5, 0, 1],
               [8, 6, 0, 1],
               [9, 7, 8]]))
    @example((EdgeLabelledGraph(graphs.CompleteGraph(5)),
              [[4, 0, 1],
               [9, 2, 3],
               [5, 4, 1, 2],
               [9, 6, 4, 1, 2],
               [7, 1, 2],
               [9, 8, 1, 2]]))
    @example((EdgeLabelledGraph(graphs.CompleteGraph(5)),
              [[7, 1, 2],
               [8, 7, 2, 3],
               [7, 4, 0, 2],
               [5, 0, 2],
               [7, 8, 6, 0, 2],
               [8, 7, 9]]))
    @example((EdgeLabelledGraph(graphs.CompleteGraph(5)),
              [[7, 1, 2],
               [9, 7, 1, 3],
               [4, 0, 1],
               [7, 5, 0, 1],
               [7, 9, 6, 0, 1],
               [9, 7, 8]]))
    @example((EdgeLabelledGraph(graphs.CompleteGraph(4)),
              [[5, 4, 0, 1], [5, 1, 2], [3, 0, 1]]))
    @example((EdgeLabelledGraph(graphs.CompleteGraph(4)),
              [[5, 1, 2], [3, 0, 1], [5, 4, 0, 1]]))
    def test_complete_graph(self, G_cycles):
        G, cycles = G_cycles
        reserved_labels = 1000
        if len(G.edge_labels()) > 0:
            reserved_labels = max(reserved_labels, max(G.edge_labels()))
        decomposition = SPQRTree(reserved_labels=reserved_labels)
        for cycle in cycles:
            self.assertTrue(decomposition.add_circuit(cycle))
            decomposition.validate()
        self.assertEqual(len(decomposition), 1)
        t0, = decomposition
        node0 = decomposition.get_node(t0)
        H = node0.graph()
        expected_edge_neighborhoods = \
            { frozenset(frozenset([G.edge_label(u,v)]) for v in G.neighbors(u))
              for u in
              G }
        actual_edge_neighborhoods = \
            { frozenset(frozenset(H.edge_label(u,v)) for v in H.neighbors(u))
              for u in H }
        self.assertEqual(actual_edge_neighborhoods,
                         expected_edge_neighborhoods)

    @given(integers(0,10))
    @example(6)
    def test_complete_graph_star(self, n):
        decomposition = SPQRTree(reserved_labels=1000)
        k = n-1
        for i in range(0,n-1):
            for j in range(i+1,n-1):
                self.assertTrue(decomposition.add_circuit([i, j, k]))
                k += 1
                decomposition.validate()

    @given(integers(0, 10))
    def test_complete_graph_path(self, n):
        decomposition = SPQRTree(reserved_labels=1000)
        k = n - 1
        for i in range(0, n - 1):
            for j in range(i + 1, n - 1):
                circuit = list(range(i, j + 1))
                circuit.append(k)
                self.assertTrue(decomposition.add_circuit(circuit))
                k += 1
                decomposition.validate()

    def test_k5(self):
        decomposition = SPQRTree(reserved_labels=1000)
        self.assertTrue(decomposition.add_circuit([0, 1, 4]))
        self.assertTrue(decomposition.add_circuit([0, 2, 5]))
        self.assertTrue(decomposition.add_circuit([0, 3, 6]))
        self.assertTrue(decomposition.add_circuit([1, 3, 8]))
        self.assertTrue(decomposition.add_circuit([2, 3, 9]))
        self.assertTrue(decomposition.add_circuit([1, 2, 7]))
        decomposition.validate()

if __name__ == '__main__':
    unittest.main()