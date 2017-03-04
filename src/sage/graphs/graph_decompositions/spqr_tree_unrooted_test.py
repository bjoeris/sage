
import sage.all
import sage.graphs.all

from sage.graphs.graph_decompositions.spqr_tree_unrooted import SPQRTree

from hypothesis import given, example

from hypothesis.strategies import integers

import unittest


class TestSPQR(unittest.TestCase):
    @given(integers(0,10))
    @example(5)
    def test_complete_graph_star(self, n):
        decomposition = SPQRTree(reserved_labels=1000)
        k = n-1
        for i in range(0,n-1):
            for j in range(i+1,n-1):
                self.assertTrue(decomposition.add_circuit([i, j, k]))
                k += 1
                for t in decomposition:
                    node = decomposition.get_node(t)
                    self.assertEqual(node.elements(),
                                     set(node.graph().edge_labels()))
                    for s in decomposition.neighbors(t):
                        m = decomposition.edge_label(s, t)
                        self.assertTrue(m in node.elements())
    @given(integers(0,10))
    def test_complete_graph_path(self, n):
        decomposition = SPQRTree(reserved_labels=1000)
        k = n-1
        for i in range(0,n-1):
            for j in range(i+1,n-1):
                circuit = list(range(i,j+1))
                circuit.append(k)
                self.assertTrue(decomposition.add_circuit(circuit))
                k += 1
    def test_k5(self):
        decomposition = SPQRTree(reserved_labels=1000)
        self.assertTrue(decomposition.add_circuit([0, 1, 4]))
        self.assertTrue(decomposition.add_circuit([0, 2, 5]))
        self.assertTrue(decomposition.add_circuit([0, 3, 6]))
        self.assertTrue(decomposition.add_circuit([1, 3, 8]))
        self.assertTrue(decomposition.add_circuit([2, 3, 9]))
        self.assertTrue(decomposition.add_circuit([1, 2, 7]))

if __name__ == '__main__':
    unittest.main()