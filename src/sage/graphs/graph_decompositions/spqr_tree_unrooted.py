# -*- coding: utf-8 -*-
r"""
A data structure representing an equivalence class of 2-isomorphic graphis.

Two graphs $G$ and $H$ are 2-isomorphic if, for each $X\subseteq E(G)$,
$X$ is the edge set of a cycle in $G$ if and only if $X$ is the edge set of
a cycle in $H$.

{INDEX_OF_METHODS}

AUTHORS:

- Benson Joeris (2017-03-11: initial version
"""

#*****************************************************************************
#      Copyright (C) 2017 Benson Joeris <bjoeris@gmail.com>
#
# Distributed  under  the  terms  of  the  GNU  General  Public  License (GPL)
#                         http://www.gnu.org/licenses/
#*****************************************************************************
from __future__ import print_function
from __future__ import absolute_import

from itertools import islice
from sage.structure.sage_object import SageObject
from sage.graphs.edge_labelled_graph import EdgeLabelledGraph

class SPQRTree(EdgeLabelledGraph):
    r"""
    A tree representing an equivalence class of 2-isomorphic graphs.
    """
    def __init__(self, reserved_labels=1000):
        """
        Construct a new, empty SPQRTree

        INPUT:
            - `reserved_labels` -- an integer greater than the largest edge
            label that will ever be added to this tree. The labels of the
            marker elements will start from this point.
        """
        self._next_marker = reserved_labels
        self._roots = set()
        super(SPQRTree, self).__init__()

    def roots(self):
        """
        Return a set of tree vertices, exactly one from each connected
        component.
        """
        return self._roots

    def add_circuit(self, elements):
        """
        Updates the decomposition so that the given elements form a cycle in
        each represented graph.

        The new set of represented graphs is the maximal set of graphs such
        that, for each represented graph $G$, `elements` is the set of edges
        in a cycle in $G$, and $G$ contains a subgraph that was represented
        by the old cycle.
        """
        if len(elements) == 0:
            return False
        elements = set(elements)
        old_elements = set()
        subtrees = []
        for root in self.roots():
            subtree, elements = self._reduced_subtree(root, elements)
            if len(subtree) == 0:
                continue

            if len(subtree) == 1:
                t0, = subtree
                node0 = self._get_node(t0)
                node0_elements = elements & node0.elements()
                if len(node0_elements) == 1:
                    e, = node0_elements
                    for t in self.get_edge(e):
                        if t is not None and self._get_node(t).is_bond():
                            subtree = {t}
                            break

            for t in subtree:
                node = self._get_node(t)
                node_elements = elements & node.elements()
                old_elements.update(node_elements)
                cycle = node.find_cycle(node_elements)
                if cycle is not None:
                    return cycle == elements

            subtree = self._subtree_path(subtree)
            if subtree is None:
                return False

            subtree = self._path_ends(subtree, elements)
            if subtree is None:
                return False

            subtrees.append((subtree, root))

        # Now we know `path_elements` can be made into a path, so it is safe
        # to start modifying the nodes

        new_elements = elements - old_elements

        glued_nodes = []
        first_subtree = True

        for subtree, root in subtrees:
            t0, end_elements0, end_vertices0 = subtree[0]
            node0 = self._get_node(t0)
            node0.rigidify_path(elements & node0.elements(), end_elements0)
            for t, end_elements, end_vertices in islice(subtree, 1, None):
                if t == root:
                    self._roots.remove(t)
                    self._roots.add(t0)
                    root = t0
                m = self.edge_label(t0, t)
                node = self._get_node(t)
                node.rigidify_path(elements & node.elements(), end_elements)
                end_vertices0 = node0.glue(node, end_vertices0, end_vertices,
                                           m in elements)
                self.validate()

            glued_nodes.append((node0, end_vertices0))

            # now `path_elements` is a path, so we just need to add `new_elements`
            if not first_subtree:
                self._roots.remove(root)
            first_subtree = False

        if len(glued_nodes) == 0:
            node = self._add_cycle_node(None, None, new_elements)
            self._roots.add(node.id())
        elif len(glued_nodes) == 1 and len(new_elements) == 1:
            (node, (u,v)), = glued_nodes
            new_e, = new_elements
            node.add_edge(u, v, new_e)
        elif len(glued_nodes) == 2 and len(new_elements) == 0:
            (node0, (u0, v0)), (node1, (u1, v1)) = glued_nodes
            m = self._new_marker()
            node0 = node0.add_edge(u0, v0, m)
            node1 = node1.add_edge(u1, v1, m)
            self.add_edge(node0.id(), node1.id(), m)
        else:
            cycle = self._add_cycle_node(None, None, new_elements)
            for node, (u,v) in glued_nodes:
                m = self._new_marker()
                cycle.add_element(m)
                node = node.add_edge(u, v, m)
                self.add_edge(node.id(), cycle.id(), m)
        return True

    def graph(self):
        G = EdgeLabelledGraph()
        def add_graph(m, H):
            if m is not None:
                uH, vH = H.get_edge(m)
                uG, vG = G.get_edge(m)
                vertex_map = { uH: uG, vH: vG }
            else:
                vertex_map = {}
            for v in H:
                if v not in vertex_map:
                    vertex_map[v] = G.add_vertex()
            G.add_edges((vertex_map[u], vertex_map[v], e)
                        for (u,v,e) in H.edge_iterator())
        for t0 in self.roots():
            stack = [(None,t0)]
            while len(stack)>0:
                m, t = stack.pop()
                add_graph(m, self._get_node(t).graph())
                for x,y,e in self.edge_boundary([t]):
                    if e == m:
                        continue
                    if x != t:
                        y = x
                    stack.append((e, y))
        return G

    def validate(self):
        """
        Do a series of integrity checks on the decomposition.
        """
        for t0 in self:
            node0 = self._get_node(t0)
            if node0.is_rigid():
                if node0.is_cycle() or node0.is_bond():
                    assert len(node0.elements()) <= 3
            assert not (node0.is_cycle() and node0.is_bond())
            assert node0.elements() == set(node0.graph().edge_labels())
            for t1 in self:
                node1 = self._get_node(t1)
                if self.has_edge(t0, t1):
                    m = self.edge_label(t0, t1)
                    assert node0.elements() & node1.elements() == {m}
                    assert not (node0.is_bond() and node1.is_bond())
                    assert not (node0.is_cycle() and node1.is_cycle())
                elif t0 != t1:
                    assert len(node0.elements() & node1.elements()) == 0

    def _new_marker(self):
        """
        Create a label for a new marker element
        """
        m = self._next_marker
        self._next_marker += 1
        return m

    def _get_node(self, t):
        """
        Get the _Node object associated with a tree vertex

        INPUT:
            - `t` -- a vertex in a tree
        """
        return self.get_vertex(t)

    def _add_cycle_node(self, parent, marker, elements):
        """
        Add a new cycle node.

        If `parent` is not `None`, the new node is attached to
        `parent` along a marker edge labelled `marker`

        INPUT:
            - `parent` -- an existing tree vertex, or `None`
            - `marker` -- a new marker label, that does not currently label
            any tree edge, or `None` if `parent` is `None`
            - `elements` -- the set of elements associated with the new node.

        OUTPUT:
            - the new node.
        """
        t = self.add_vertex()
        node = SPQRTree._Node.Cycle(self, t, elements)
        self.set_vertex(t, node)
        if parent is not None:
            self.add_edge(parent, t, marker)
        return node

    def _add_bond_node(self, parent, marker, elements):
        """
        Add a new bond node.

        If `parent` is not `None`, the new node is attached to
        `parent` along a marker edge labelled `marker`

        INPUT:
            - `parent` -- an existing tree vertex, or `None`
            - `marker` -- a new marker label, that does not currently label
            any tree edge, or `None` if `parent` is `None`
            - `elements` -- the set of elements associated with the new node.

        OUTPUT:
            - the new node.
        """
        t = self.add_vertex()
        node = SPQRTree._Node.Bond(self, t, elements)
        self.set_vertex(t, node)
        self.add_edge(parent, t, marker)
        return node

    def _move_edge(self, e, t_old, t_new):
        """
        Move one end of a tree edge.

        INPUT:
            - `e` -- the edge label of the tree edge to be moved.
            - `t_old` -- the tree node currently incident with `e`,
            which will no longer be incident with `e`
            - `t_new` -- the tree node that will become incident with `e`
        """
        t, s = self.get_edge(e)
        if t is not None:
            if t != t_old:
                t, s = s, t
            assert t == t_old
            self.delete_edge(t_old, s, e)
            self.add_edge(t_new, s, e)

    def _reduced_subtree(self, root, elements):
        """
        Find the minimal relevant subtree for `add_circuit`.

        This creates a set `reduced_elements`, such that, in each graph
        represented by this decomposition, `reduced_elements` is the edge
        set of a path if and only if `elements` is the edge set of a path,
        and `reduced_elements` is a small as possible.

        This also finds the minimal subtree containing the nodes whose
        element sets contain an element of `reduced_elements`.

        OUTPUT:
            - A pair `(subtree, reduced_elements)`, where `subtree` is the
            set of tree vertices in the minimal subtree,
            and `reduced_elements` is the reduced set of elements.
        """
        assert len(self) > 0
        subtree = set()

        def reduce_cycle(node, m):
            node_elements = node.elements() & elements
            if len(node_elements) == 0:
                return True
            elif m in node_elements:
                return node_elements == {m}
            C = node.find_cycle(node_elements | {m})
            if C is not None:
                if m in C:
                    elements.symmetric_difference_update(C)
                    return (len(C) == len(node_elements) + 1)
            return False

        def recurse(p, t):
            node = self._get_node(t)
            in_subtree = p is None
            for s in self.neighbors(t):
                if s != p:
                    in_subtree |= recurse(t, s)
            if p is not None:
                marker = self.edge_label(p, t)
                in_subtree |= not reduce_cycle(node, marker)
            if in_subtree:
                subtree.add(t)
            return in_subtree

        recurse(None, root)

        # the root is pulled into the subtree initially, but may not
        # actually belong. Try to reduce cycles down as long as it has
        # exactly one child
        t = root
        while True:
            subtree_children = [s for s in self.neighbors(t)
                                if s in subtree]
            if len(subtree_children) == 1:
                s, = subtree_children
                marker = self.edge_label(t, s)
                if reduce_cycle(self._get_node(t), marker):
                    subtree.remove(t)
                    t = s
                    continue
            break

        if len(subtree) == 1:
            t, = subtree
            node = self._get_node(t)
            if len(node.elements() & elements) == 0:
                subtree = set()

        # subtree now contains the correct set of reduced subtree nodes.
        return subtree, elements

    def _divide_elements(self, elements, subtree):
        """
        Divide the `elements` set into two: the old elements, found in
        some node in `subtree`, and the new elements, not found in any
        node in `subtree`.
        """
        old_elements = set()
        for t in subtree:
            node = self._get_node(t)
            node_elements = node.elements() & elements
            old_elements.update(node_elements)
        elements.difference_update(old_elements)
        return old_elements, elements

    def _subtree_path(self, subtree):
        """
        Check that the subtree is a path and return a sorted list of the
        nodes along the path, or return None if it is not a path.
        """
        if len(subtree) == 1:
            return list(subtree)
        t0 = None
        for t in subtree:
            neighbors = [s for s in self.neighbors(t) if s in subtree]
            if len(neighbors) == 1:
                # found a leaf of the subtree
                t0 = t
                break
        if t0 is None:
            return None
        p = None
        t = t0
        subtree_list = []
        while True:
            subtree_list.append(t)
            subtree_children = [s for s in self.neighbors(t)
                                if s in subtree and s != p]
            if len(subtree_children) == 0:
                # we reached the other end of the path
                break
            elif len(subtree_children) == 1:
                p, t = t, subtree_children[0]
            else:
                # subtree isn't a path, so it is impossible to add these
                # elements as a circuit
                return None
        return subtree_list

    def _path_ends(self, subtree, path_elements):
        """
        Find the ends of the segments of the path in each node in the subtree.

        If this decomposition represents a graph in which `path_elements` is
        the edge set of a path, then find, for each node in `subtree`,
        the two vertices that are the ends of the subpath in the graph
        associated with that node.

        INPUT:
            - `subtree` -- a list of nodes which form a path in a
            decomposition tree.
            - `path_elements` -- a set of elements contained in the union of
            the element sets associated with the nodes in `subtree`.

        OUTPUT:
            - A list of triples, `(t, end_elements, end_verts)`, where `t`
            is a tree-vertex, `end_elements` is a pair in which each item is
            either an element of the node associated with `t`, or `None`, and
            `end_verts` is a pair of vertices in the graph associated with `t`.
        """
        n = len(subtree)
        for i, t in enumerate(subtree):
            node = self._get_node(t)
            e1, e2 = None, None
            if i > 0:
                t_prev, _, _ = subtree[i-1]
                e1 = self.edge_label(t_prev, t)
            if i+1 < n:
                t_next = subtree[i+1]
                e2 = self.edge_label(t_next, t)
            end_elements = e1, e2
            end_verts = node.path_end_verts(path_elements & node.elements(),
                                            end_elements)
            if end_verts is None:
                return None
            subtree[i] = t, end_elements, end_verts
        return subtree

    class _Node(SageObject):

        CYCLE = 1
        BOND = 2
        RIGID = 4

        def __init__(self, owner, id):
            self._owner = owner
            self._id = id
            self._kind = 0
            self._graph = None
            self._elements = set()

        @staticmethod
        def Cycle(owner, id, elements):
            node = SPQRTree._Node(owner, id)
            node._kind = SPQRTree._Node.CYCLE
            if len(elements) < 4:
                node._kind |= SPQRTree._Node.RIGID
            node._elements.update(elements)
            return node

        @staticmethod
        def Bond(owner, id, elements):
            node = SPQRTree._Node(owner, id)
            node._kind = SPQRTree._Node.BOND
            if len(elements) < 4:
                node._kind |= SPQRTree._Node.RIGID
            node._elements.update(elements)
            return node

        @staticmethod
        def Rigid(owner, id, graph):
            node = SPQRTree._Node(owner, id)
            node._kind = SPQRTree._Node.RIGID
            node._graph = graph
            node._elements.update(graph.edge_labels())
            return node

        def is_cycle(self):
            """
            Returns whether this is a cycle node.
            """
            return self._kind & SPQRTree._Node.CYCLE != 0

        def is_bond(self):
            """
            Returns whether this is a bond node.
            """
            return self._kind & SPQRTree._Node.BOND != 0

        def is_rigid(self):
            """
            Returns whether this is a rigid (3-connected) node.
            """
            return self._kind & SPQRTree._Node.RIGID != 0

        def graph(self):
            """
            Returns one possible graph represented by this node.
            """
            if self._graph is None:
                self._make_graph()
            return self._graph

        def elements(self):
            """
            Returns the set of elements associated with this node.

            This is the set of edges of graphs represented by this node.

            This includes marker elements for attachements to other nodes.
            """
            return self._elements

        def owner(self):
            """
            The SPQRTree which this node is a part of.
            """
            return self._owner

        def id(self):
            """
            The name of the vertex associated with this node in `self.owner()`.
            """
            return self._id

        def find_cycle(self, elements):
            """
            Searches for a cycle in a subset of the elements of this node.

            INPUT:
                - `elements` -- a subset of self.elements().

            OUTPUT:
                - A subset of `elements` that induces a cycle in the graphs
                represented by this node.
                - If no such subset exists, returns `None`.
            """
            assert elements <= self.elements()
            if self.is_bond():
                if len(elements) >= 2:
                    return set(islice(elements, 2))
                else:
                    return None
            elif self.is_cycle():
                if len(elements) == len(self.elements()):
                    return elements
                else:
                    return None
            else:
                G = self.graph()
                vertices = G.vertices_incident(elements)
                H = G.subgraph(vertices,
                               (G.get_edge(e, labelled=True) for e in
                                elements))
                _, cycle = H.is_forest(certificate=True, output='edge')
                if cycle is None:
                    return None
                else:
                    return set(e for _, _, e in cycle)

        def delete_edge(self, e):
            """
            Removes an element from this node.

            INPUT:
                - `e` -- the element to be removed. This must be in
                `self.elements()`
            """
            self._elements.remove(e)
            if self._graph is not None:
                G = self.graph()
                u, v = G.get_edge(e)
                if u is not None:
                    G.delete_edge(u, v, e)

        def _add_edge(self, u, v, e):
            """
            Adds an edge to this node.

            INPUT:
                - `u, v` -- the vertices incident with the edge. These should be
                  vertices of `self.graph()`.
                - `e` -- the label of the edge
            """
            self._elements.add(e)
            G = self.graph()
            G.add_edge(u, v, e)

        def _add_edges(self, edges):
            """
            Add a collection of edges to this node.

            INPUT:
                - `edges` -- An iterable collection of tuples of the form
                `(u,v,e)`, where `u` and `v` ar the vertices incident with the
                edge, and `e` is the label of the edge.
            """
            edges = list(edges)
            self._elements.update((e for _, _, e in edges))
            self.graph().add_edges(edges)

        def add_element(self, e_new):
            """
            Add a new element to this node.

            This only works for cycle or bond nodes.

            INPUT:
                - `e_new` -- the new element to be added
            """
            assert self.is_cycle() or self.is_bond()
            self._elements.add(e_new)
            if len(self.elements()) > 3:
                self._kind &= ~SPQRTree._Node.RIGID
            self._graph = None
            return self

        def add_edge(self, u, v, e_new):
            """
            Add an edge to this node.

            This may involve adding additional nodes to the tree.

            INPUT:
                - `u, v` -- the vertices incident with the new edge
                - `e_new` -- the label of the new edge. This should not already
                be in the element set of any node in the tree.
            """
            if self.is_bond():
                return self.add_element(e_new)
            G = self.graph()
            owner = self.owner()
            if not G.has_edge(u, v):
                self._add_edge(u, v, e_new)
                return self
            else:
                e_old, = G.edge_label(u, v)
                s, t = owner.get_edge(e_old)
                if s is not None:
                    if s != self.id():
                        s, t = t, s
                    other = owner._get_node(t)
                    if other.is_bond():
                        return other.add_element(e_new)
                m = owner._new_marker()
                self.delete_edge(e_old)
                self._add_edge(u, v, m)
                new_node = owner._add_bond_node(self.id(), m, {e_old, e_new, m})
                owner._move_edge(e_old, self.id(), new_node.id())
                return new_node

        def add_path(self, u, v, new_elements):
            """
            Add a path, with endpoints in this this node.

            This may involve adding additional nodes to the tree.

            INPUT:
                - `u, v` -- the ends of the path
                - `new_elements` -- an iterable collection of elements. These
                elements should not already be in the element set of any nodes
                in the tree.
            """
            owner = self.owner()
            if len(new_elements) == 1:
                e, = new_elements
                return self.add_edge(u, v, e)
            else:
                m = owner._new_marker()
                t = self.add_edge(u, v, m).id()
                new_elements.add(m)
                return owner._add_cycle_node(t, m, new_elements)

        def path_end_verts(self, path_elements, end_elements):
            """
            Searches for a pair of vertices that are possible end points of a path.

            The edges of the path must be exactly the set `path_elements`,
            and the ends of the path must be incident with the edges in
            `end_elements`.

            INPUT:
                - `path_elements` -- a set consisting of the edges of the
                desired path. This must be a subset of `self.elements()`
                edge set of the desired path
                - `end_elements` -- a pair, each either an element in
                `self.elements()` or `None`; if not `None`, the beginning/end of
                the path must be incident with the specified element.

            OUTPUT:
                - A pair `(u,v)` of vertices in `self.graph()`, which are the
                beginning and end of the desired path, respectively.
                - If no such path exists, returns `None`
            """
            assert path_elements <= self.elements()
            end_element_set = set(e for e in end_elements if e is not None)
            if self.is_bond():
                if len(path_elements) == 0:
                    return (0, 0)
                elif len(path_elements) == 1:
                    return (0, 1)
                else:
                    return None
            elif self.is_cycle():
                if len(path_elements) == 0:
                    return (0, 0)
                elif len(path_elements) < len(self.elements()):
                    if path_elements <= end_element_set:
                        return (0, len(path_elements))
                    else:
                        ends_in_path = path_elements & end_element_set
                        return (0, 1 + len(ends_in_path))
                else:
                    return None
            G = self.graph()
            if len(path_elements) == 0:
                assert len(end_element_set) == 2
                e1, e2 = end_elements
                common_verts = set(G.get_edge(e1))
                common_verts.intersection_update(G.get_edge(e2))
                v = next(iter(common_verts))
                return (v, v)
            vertices = G.vertices_incident(path_elements)
            edges = [G.get_edge(e, labelled=True) for e in path_elements]
            if len(vertices) != len(edges) + 1:
                return None
            P = G.subgraph(vertices, edges)
            if not P.is_connected():
                return None
            end_vert_set = set()
            for v in P:
                d = P.degree(v)
                if d <= 1:
                    end_vert_set.add(v)
                elif d > 2:
                    return None
            end_verts = []
            for e in end_elements:
                if e is not None:
                    verts_incident = end_vert_set.intersection(G.get_edge(e))
                    if len(verts_incident) == 0:
                        return None
                    elif len(verts_incident) == 1:
                        v, = verts_incident
                        end_vert_set.remove(v)
                        end_verts.append(v)
                        continue
                end_verts.append(None)
            for i, v in enumerate(end_verts):
                if v is None:
                    v = end_vert_set.pop()
                    end_verts[i] = v
            return tuple(end_verts)

        def split(self, elements):
            """
            Split off a subset of elements, creating a new node.

            INPUT:
                - `elements` -- an iterable collection containing the elements
                to be split off from this node.

            OUTPUT:
                - the marker element of the new node containing `elements`
                - If `len(elements)== 1`, no new node is actually created,
                and the single element is returned.
            """
            elements = set(elements)
            assert elements <= self.elements()
            assert len(elements) > 0
            assert self.is_bond() or self.is_cycle()
            if len(elements) == 1:
                e, = elements
                return e
            owner = self.owner()
            self._elements.difference_update(elements)
            m = owner._new_marker()
            self._elements.add(m)
            elements.add(m)
            self._graph = None
            if self.is_bond():
                t_new = owner._add_bond_node(self.id(), m, elements).id()
            else:
                t_new = owner._add_cycle_node(self.id(), m, elements).id()
            for e in elements:
                if e == m:
                    continue
                s, t = owner.get_edge(e)
                if s is not None:
                    if s == self.id():
                        s, t = t, s
                    owner.delete_edge(t, s, e)
                    owner.add_edge(t_new, s, e)
            return m

        def become_rigid(self, graph):
            """
            Replace this node by a rigid node with the given graph.

            INPUT:
                - `graph` -- the graph representing the rigid node. The set of
                edge labels of this graph must be `self.elements()`
            """
            self._graph = graph
            self._kind = SPQRTree._Node.RIGID

        def become_bond(self):
            """
            Make this node into a bond node.
            """
            self._kind = SPQRTree._Node.BOND
            if len(self.elements()) < 4:
                self._kind |= SPQRTree._Node.RIGID

        def become_cycle(self):
            """
            Make this node into a cycle node.
            """
            self._kind = SPQRTree._Node.CYCLE
            if len(self.elements()) < 4:
                self._kind |= SPQRTree._Node.RIGID

        def rigidify_path(self, path_elements, end_elements):
            """
            Replace this node with a node in which `path_elements` is the edge
            set of a path with ends incident with the edges in `end_elements`.

            This assumes the path exists. This should already have been checked
            using `path_end_verts`.

            INPUT:
                - `path_elements` -- a set, consisting of the edges of the
                desired path.
                - `end_elements` -- a pair, each either in `self.elements()` or
                `None`; if not `None`, the beginning/end of the path must be
                incident with the specified element.
            """
            assert path_elements <= self.elements()
            end_element_set = set(e for e in end_elements if e is not None)
            if self.is_bond():
                if len(end_element_set) == 2 and len(self.elements()) > 3:
                    self.split(self.elements() - end_element_set)
            elif self.is_cycle():
                def cycle_graph(edges):
                    n = len(edges)
                    G = EdgeLabelledGraph(multiedges=True)
                    G.add_vertices(range(n))
                    G.add_edges(
                        (i, (i + 1) % n, e) for i, e in enumerate(edges))
                    return G

                if len(path_elements) == len(self.elements()) - 1 and \
                                len(end_element_set) == 0:
                    e0, = self.elements() - path_elements
                    graph_edges = [e0] + list(path_elements)
                    self._graph = cycle_graph(graph_edges)
                    return

                anti_path_elements = self.elements() - \
                                     (path_elements | end_element_set)
                only_path_elements = path_elements - end_element_set
                e4, e2 = end_elements
                e1, e3 = None, None
                if len(only_path_elements) > 0:
                    e1 = self.split(only_path_elements)
                if len(anti_path_elements) > 0:
                    e3 = self.split(anti_path_elements)
                graph_edges = [e for e in [e1, e2, e3, e4] if e is not None]
                if e4 in path_elements:
                    graph_edges = graph_edges[-1:] + graph_edges[0:-1]
                self.become_rigid(cycle_graph(graph_edges))
                if len(graph_edges) <= 2:
                    self.become_bond()
                elif len(graph_edges) == 3:
                    self.become_cycle()

        def glue(self, other, self_end_verts, other_end_verts, flipped=False):
            """
            Glue this node to another node.

            The two nodes must share a common marker edge. The edges incident
            with this marker in the two graphs are identified so that
            `self_end_verts[1]` is identified with `other_end_verts[0]`.

            INPUT:
                - `other` -- a node. This must be a neighbor of `self` in the
                tree containing `self`.
                - `self_end_verts` -- a pair of vertices in `self.graph()` which
                are the beginning/end of a path in `self.graph()`.  The second
                (end) vertex in the pair must be incident with the marker
                element connecting `self` to `other` in the tree.
                - `other_end_verts` -- a pair of vertices in `other.graph()` which
                are the beginning/end of a path in `other.graph()`.  The second
                (end) vertex in the pair must be  incident with the marker
                element connecting `self` to `other` in the tree.
                - `flipped` -- if `True`, the identification of the vertices is
                reversed, so `self_end_verts[1]` is identified with the other
                vertex incident with the marker, not `other_end_verts[0]`.
            """
            G = self.graph()
            H = other.graph()
            owner = self.owner()
            m = owner.edge_label(self.id(), other.id())

            uG, vG = G.get_edge(m)
            if uG != self_end_verts[1]:
                uG, vG = vG, uG
                assert uG == self_end_verts[1]

            uH, vH = H.get_edge(m)
            if uH != other_end_verts[0]:
                uH, vH = vH, uH
                assert uH == other_end_verts[0]

            if flipped:
                vertex_map = {uH: vG, vH: uG}
            else:
                vertex_map = {uH: uG, vH: vG}

            self.delete_edge(m)
            other.delete_edge(m)

            for v in H:
                if v != uH and v != vH:
                    vertex_map[v] = G.add_vertex()
            self._add_edges((vertex_map[u], vertex_map[v], e)
                            for u, v, e in H.edge_iterator())
            self.become_rigid(G)
            owner.merge_vertices([self.id(), other.id()])

            return self_end_verts[0], vertex_map[other_end_verts[1]]

        def __len__(self):
            return len(self._elements)

        def _make_graph(self):
            """
            Constructs a graph representing this node.

            In general the vertices of this graph are arbitrary, and, in the
            case of a cycle node, the ordering of the edges around the cycle is
            also arbitrary.
            """
            self._graph = EdgeLabelledGraph(multiedges=True)
            if len(self) == 0:
                return
            if self.is_bond():
                self._graph.add_vertices([0, 1])
                self._graph.add_edges((0, 1, e) for e in self._elements)
            elif self.is_cycle():
                n = len(self)
                self._graph.add_vertices(range(n))
                edges = ((i, (i + 1) % n, e) for i, e in
                         enumerate(self._elements))
                self._graph.add_edges(edges)
            else:
                raise Exception("cannot call _make_graph on rigid node")
