# -*- coding: utf-8 -*-
r"""
Undirected, edge-labelled graphs.

This module implements functions and operations involving undirected
graphs with labelled edges.

Unlike ordinary Sage graphs, each edge in an edge-labelled graph has
a distinct label.

{INDEX_OF_METHODS}

AUTHORS:

- Benson Joeris (2017-02-20: initial version
"""

#*****************************************************************************
#      Copyright (C) 2017 Benson Joeris <bjoeris@gmail.com>
#
# Distributed  under  the  terms  of  the  GNU  General  Public  License (GPL)
#                         http://www.gnu.org/licenses/
#*****************************************************************************
from __future__ import print_function, division
from __future__ import absolute_import

from sage.graphs.graph import Graph
from sage.graphs.digraph import DiGraph

class EdgeLabelledMixin(object):
    r"""
    Undirected, edge-labelled graph.

    An edge-labelled graph is a pair of sets $(V,E)$, (the *vertices*
    and *edges*, respectievly) and a relation on $V\times E$, called
    *incidence*, where each edge $e\in E$ is *incident* with either 1
    or 2 vertices in $V$.

    In graph construction and mutation, unlabelled edges will be
    assigned a new, integer label.

    The arguments to the EdgeLabelledGraph constructor are identical
    to those of the Graph constructor.

    By default, edge-labelled graphs allow neither *loops* (i.e.,
    an edge incident with exactly one vertex) or *multiple edges* (
    i.e. multiple edges incident with the same pair of vertices),
    but these can be turned on using the ``loops``  and
    ``multiedges`` flags, respectively.

    TESTS::

        sage: TestSuite(EdgeLabelledGraph()).run()
        sage: TestSuite(EdgeLabelledDiGraph()).run()
    """

    def __init__(self, reserved_edge_labels):
        self._vertices_incident = dict()
        if reserved_edge_labels is not None:
            self._next_edge_label = reserved_edge_labels
        else:
            self._next_edge_name = 0

    def get_edge(self, edge_label, labelled=False):
        """
        Returns the vertices incident with an edge.

        INPUT:

        - ``edge_label`` -- an edge label

        OUTPUT:

        A pair ``(u,v)`` such that:
        - if ``edge_label`` is the label of a non-loop edge, then
        ``u`` and ``v`` are the two vertices incident with the edge,
        - if ``edge_label`` is the label of a loop edge, then ``u ==
        v`` and ``u`` is the label of the unique vertex incident with
        the edge.
        - if ``edge_label`` is not the label of an edge, then ``u``
        and ``v`` are both ``None``.

        EXAMPLES:

        Add an edge with an explicit label.

        ::

            sage: G = EdgeLabelledGraph()
            sage: G.add_vertex(0)
            sage: G.add_vertex(1)
            sage: G.add_edge(0, 1, 'e')
            sage: G.get_edge('e')
            (0, 1)
            sage: G.get_edge('f')
            (None, None)
        """
        vertices = self._vertices_incident.get(edge_label)
        if vertices is not None:
            u, v = vertices
            if labelled:
                return u, v, edge_label
            else:
                return u, v
        elif labelled:
            return None, None, edge_label
        else:
            return None, None

    def vertices_incident(self, edge_labels):
        """
        Returns vertices incident to an edge or edges.

        INPUT:

        - ``edge_labels`` -- an iterable collection of edge labels.
        Any elements in the collection that are not edge labels in
        the graph are ignored.

        OUTPUT:

        The set of vertices that are incident with at least one edge
        in ``edge_labels``.
        """
        vertices = set()
        for e in edge_labels:
            e_verts = self._vertices_incident.get(e)
            if e_verts is not None:
                vertices.update(e_verts)
        return vertices

    def add_edge(self, u, v=None, label=None):
        """
        Adds an edge from ``u`` to ``v``, with an optional label. If
        no label is provided, a new label will be generated.

        EXAMPLES:

        Add an edge with an explicit label.

        ::

            sage: G = EdgeLabelledGraph()
            sage: G.add_vertex(0)
            sage: G.add_vertex(1)
            sage: G.add_edge(0, 1, 'e')
            sage: G.edges()
            [(0, 1, 'e')]

        Add an edge without an explicit label; a new edge label is
        created

        ::

            sage: G = EdgeLabelledGraph()
            sage: G.add_vertex(0)
            sage: G.add_vertex(1)
            sage: G.add_edge(0, 1)
            sage: G.edges()
            [(0, 1, 0)]

        .. SEALSO:
            :meth:`sage.graphs.generic_graph.GenericGraph.add_edge`
        """
        if label is None:
            if v is None:
                try:
                    u, v, label = u
                except Exception:
                    u, v = u
                    label = None
        if label in self._vertices_incident:
            up, vp = self._vertices_incident[label]
            assert {u,v} == {up, vp}, \
                "Duplicate edge label incident with different vertices in EdgeLabelledGraph"
            return
        if label is None:
            label = self._get_new_edge()
        self._vertices_incident[label] = (u, v)
        super(EdgeLabelledMixin, self).add_edge(u, v, label)

    def add_edges(self, edges):
        """
        Add edges from an iterable container. If the edges do not
        have edge labels, new edge labels will be generated

        EXAMPLES:

        Add edges with explicit labels

        ::

            sage: G = EdgeLabelledGraph()
            sage: G.add_vertex(0)
            sage: G.add_vertex(1)
            sage: G.add_vertex(2)
            sage: G.add_edges([(0, 1, 'a'), (0, 2, 'b')])
            sage: G.edges()
            [(0, 1, 'a'), (0, 2, 'b')]
            sage: G.get_edge('a')
            (0, 1)
            sage: G.get_edge('b')
            (0, 2)

        Add edges without explicit labels; new edge labels are created

        ::

            sage: G = EdgeLabelledGraph()
            sage: G.add_vertex(0)
            sage: G.add_vertex(1)
            sage: G.add_vertex(2)
            sage: G.add_edges([(0, 1), (0, 2)])
            sage: G.edges()
            [(0, 1, 0), (0, 2, 1)]
            sage: G.get_edge(0)
            (0, 1)
            sage: G.get_edge(1)
            (0, 2)

        .. SEALSO:
            :meth:`sage.graphs.generic_graph.GenericGraph.add_edges`
        """
        labelled_edges = []
        for edge in edges:
            try:
                u, v, e = edge
            except Exception:
                u, v = edge
                e = None

            if e in self._vertices_incident:
                up, vp = self._vertices_incident[e]
                assert {u, v} == {up, vp}, \
                    "Duplicate edge label incident with different vertices in EdgeLabelledGraph"
                continue
            if e is None:
                e = self._get_new_edge()
            self._vertices_incident[e] = (u, v)
            labelled_edges.append((u, v, e))
        super(EdgeLabelledMixin, self).add_edges(labelled_edges)

    def delete_vertex(self, vertex, in_order=False):
        """
        Delete a vertex, removing all incident edges.

        EXAMPLES:

        Delete a vertex

        ::

            sage: G = EdgeLabelledGraph()
            sage: G.add_vertex(0)
            sage: G.add_vertex(1)
            sage: G.add_vertex(2)
            sage: G.add_edges([(0, 1, 'a'), (0, 2, 'b'), (1, 2, 'c')])
            sage: G.delete_vertex(0)
            sage: G.edges()
            [(1, 2, 'c')]
            sage: G.get_edge('a')
            (None, None)
            sage: G.get_edge('b')
            (None, None)
            sage: G.get_edge('c')
            (1, 2)

        .. SEALSO:
            :meth:`sage.graphs.generic_graph.GenericGraph.delete_vertex`
        """
        if in_order:
            v = self.vertices()[vertex]
        else:
            v = vertex
        for _,_,e in self.edges_incident(v):
            del self._vertices_incident[e]
        super(EdgeLabelledMixin, self).delete_vertex(vertex, in_order)

    def delete_vertices(self, vertices):
        """
        Remove vertices from the graph from an iterable container of
        vertices.

        EXAMPLES:

        Delete two vertices

        ::

            sage: G = EdgeLabelledGraph()
            sage: G.add_vertex(0)
            sage: G.add_vertex(1)
            sage: G.add_vertex(2)
            sage: G.add_vertex(3)
            sage: G.add_edges([(0, 1, 'a'), (0, 2, 'b'), (0, 3, 'c'),
            ....:             (1, 2, 'd'), (1, 3, 'e'), (2, 3, 'f')])
            sage: G.delete_vertices([2, 3])
            sage: G.edges()
            [(0, 1, 'a')]
            sage: G.get_edge('a')
            (0, 1)
            sage: G.get_edge('b')
            (None, None)

        .. SEALSO:
            :meth:`sage.graphs.generic_graph.GenericGraph.delete_vertices`
        """
        for v in vertices:
            for _, _, e in self.edges_incident([v]):
                self._vertices_incident.pop(e, None)
        super(EdgeLabelledMixin, self).delete_vertices(vertices)

    def delete_edge(self, u, v=None, label=None):
        """
        Delete the edge from ``u`` to ``v``, with an optionally
        specified label.

        If there are multiple edges between ``u`` and ``v` and the
        edge label is unspecified, exactly one of the edges will be
        removed, chosen arbitrarily.

        EXAMPLES:

        Delete an edge with an explicit label

        ::

            sage: G = EdgeLabelledGraph()
            sage: G.add_vertex(0)
            sage: G.add_vertex(1)
            sage: G.add_vertex(2)
            sage: G.add_edges([(0, 1, 'a'), (0, 2, 'b'), (1, 2, 'c')])
            sage: G.delete_edge(0, 1, 'a')
            sage: G.edges()
            [(0, 2, 'b'), (1, 2, 'c')]
            sage: G.get_edge('a')
            (None, None)
            sage: G.get_edge('b')
            (0, 2)

        Delete an edge with no explicit label

        ::

            sage: G = EdgeLabelledGraph(multiedges=True)
            sage: G.add_vertex(0)
            sage: G.add_vertex(1)
            sage: G.add_edges([(0, 1, 'a'), (0, 1, 'b'), (0, 1, 'c')])
            sage: G.delete_edge(0, 1)
            sage: G.edges()
            [(0, 1, 'a'), (0, 1, 'b')]
            sage: G.get_edge('a')
            (0, 1)
            sage: G.get_edge('b')
            (0, 1)
            sage: G.get_edge('c')
            (None, None)

        .. SEALSO:
            :meth:`sage.graphs.generic_graph.GenericGraph.delete_edge`
        """
        if label is None:
            if v is None:
                try:
                    u, v, label = u
                except Exception:
                    u, v = u
                    label = None

        if not self.has_edge(u,v):
            return
        if label is None:
            label = self.edge_label(u, v)
            if label is None:
                # not adjacent
                return
            elif self.allows_multiple_edges():
                label = label[0]
        del self._vertices_incident[label]
        super(EdgeLabelledMixin, self).delete_edge(u, v, label)

    def edge_label_set(self):
        return self._vertices_incident.viewkeys()

    def edge_labels(self):
        return list(self.edge_label_set())

    def _get_new_edge(self):
        """
        Returns a new edge label, safe to use for a new edge
        """
        e = self._next_edge_name
        self._next_edge_name += 1
        while e in self._vertices_incident:
            e = self._next_edge_name
            self._next_edge_name += 1
        return e

class EdgeLabelledGraph(EdgeLabelledMixin, Graph):
    def __init__(self, *args, **kwargs):
        reserved_edge_labels = kwargs.pop("reserved_edge_labels", None)
        EdgeLabelledMixin.__init__(self, reserved_edge_labels)
        Graph.__init__(self, *args, **kwargs)

class EdgeLabelledDiGraph(EdgeLabelledMixin, DiGraph):
    def __init__(self, *args, **kwargs):
        reserved_edge_labels = kwargs.pop("reserved_edge_labels", None)
        EdgeLabelledMixin.__init__(self, reserved_edge_labels)
        DiGraph.__init__(self, *args, **kwargs)