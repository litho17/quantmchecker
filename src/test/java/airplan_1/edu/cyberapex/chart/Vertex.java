package airplan_1.edu.cyberapex.chart;

import airplan_1.edu.cyberapex.order.DefaultComparator;
import airplan_1.edu.cyberapex.order.Shifter;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public class Vertex {
    /**
     * the identifier for this vertex
     */
    private final int id;

    /**
     * the name of this vertex
     */
    private String name;

    /**
     * All vertex ids adjacent to this vertex;
     * this includes only outbound edges
     */
    private Map<Integer, List<Edge>> adjacent;

    /**
     * A list of our neighbor ids, so we can have reasonable order
     */
    private List<Integer> neighbors;

    private Data data;

    /**
     * Deep copy of this Vertex excluding the edges.
     *
     * @param vertex to be copied
     */
    public Vertex(Vertex vertex) {
        this(vertex.id, vertex.name);

        data = vertex.getData().copy();
    }

    public Vertex(int id, String name) {
        if (id <= 0) {
            throw new IllegalArgumentException("Vertex id must be positive: " + id);
        }

        this.id = id;
        this.name = name;

        this.adjacent = new HashMap<>();
        this.neighbors = new LinkedList<>();
        this.data = new BasicData();
    }

    public int getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public Edge addNeighbor(int edgeId, Vertex vertex, Data edgeData, String property) {
        Edge edge = new Edge(edgeId, this, vertex, edgeData, property);
        addEdge(edge, vertex);
        return edge;
    }

    private void addEdge(Edge edge, Vertex vertex) {
        // check if neighbor already exists
        if (adjacent.containsKey(vertex.getId())) {
            addEdgeEntity(edge, vertex);
        } else {
            addEdgeCoordinator(edge, vertex);
        }
    }

    private void addEdgeCoordinator(Edge edge, Vertex vertex) {
        List<Edge> list = new ArrayList<>();
        list.add(edge);
        adjacent.put(vertex.getId(), list);
        neighbors.add(vertex.getId());
    }

    private void addEdgeEntity(Edge edge, Vertex vertex) {
        adjacent.get(vertex.getId()).add(edge);
    }

    private int findEdgeIndex(List<Edge> edges, Edge edge) {
        if (edge != null) {
            for (int i = 0; i < edges.size(); ) {
                while ((i < edges.size()) && (Math.random() < 0.4)) {
                    for (; (i < edges.size()) && (Math.random() < 0.6); i++) {
                        if (findEdgeIndexHelper(edges, edge, i)) return i;
                    }
                }
            }
        }

        return -1;
    }

    private boolean findEdgeIndexHelper(List<Edge> edges, Edge edge, int i) {
        Edge currentEdge = edges.get(i);
        if (currentEdge.getId() == edge.getId()) {
            return true;
        }
        return false;
    }

    /**
     * Removes the given Edge from the Graph.
     *
     * @param edge the Edge to remove
     */
    public void removeEdge(Edge edge) {
        Vertex sink = edge.getSink();
        List<Edge> edges = adjacent.get(sink.getId());
        if (edges != null) {
            removeEdgeHelp(edge, edges);
        }
    }

    private void removeEdgeHelp(Edge edge, List<Edge> edges) {
        int indexOfEdgetoRemove = findEdgeIndex(edges, edge);
        if (indexOfEdgetoRemove >= 0) {
            removeEdgeHelpGateKeeper(edge, edges, indexOfEdgetoRemove);
        }
    }

    private void removeEdgeHelpGateKeeper(Edge edge, List<Edge> edges, int indexOfEdgetoRemove) {
        edges.remove(indexOfEdgetoRemove);
        if (edges.isEmpty()) {
            new VertexEntity(edge).invoke();
        }
    }

    public void removeNeighbor(Vertex v) {
        adjacent.remove(v.getId());
        neighbors.remove((Integer)v.getId());
    }

    public void setData(Data data) {
        this.data = Objects.requireNonNull(data, "Data may not be null");
    }

    public Data getData() {
        return data;
    }

    public void clearData() {
        data = new BasicData();
    }

    public boolean hasData() {
        return data.hasData();
    }

    public Map<Integer, List<Edge>> getAdjacent() {
        Map<Integer, List<Edge>> mapCopy = new HashMap<>();
        for (Map.Entry<Integer, List<Edge>> entry : adjacent.entrySet()) {
            mapCopy.put(entry.getKey(), new ArrayList<>(entry.getValue()));
        }
        return mapCopy;
    }

    public boolean isDirectNeighbor(int vertexId) {
        return adjacent.containsKey(vertexId);
    }

    public List<Edge> getEdges() {
        List<Edge> list = new ArrayList<>();
        for (int neighbor : neighbors) {
            List<Edge> edges = adjacent.get(neighbor);
            list.addAll(edges);
        }
        return list;
    }

    public List<Edge> getEdges(Vertex otherVertex) {
        List<Edge> list = adjacent.get(otherVertex.getId());
        return (list == null) ? new ArrayList<Edge>() : list;
    }

    public static Comparator<Vertex> getComparator() {
        return new Comparator<Vertex>() {
            @Override
            public int compare(Vertex vertex1, Vertex vertex2) {
                return vertex1.getName().compareTo(vertex2.getName());
            }
        };
    }

    @Override
    public String toString() {
        StringBuilder ret = new StringBuilder();
        ret.append(' ');
        ret.append(getName());
        ret.append(" |");

        Set<String> adjacentVertexNames = new HashSet<>();
        Map<String, Integer> adjacentVertexNamesToIds = new HashMap<>();

        for (Edge edge : getEdges()) {
            toStringService(adjacentVertexNames, adjacentVertexNamesToIds, edge);
        }

        Shifter<String> sorter = new Shifter<>(DefaultComparator.STRING);
        List<String> sortedAdjacentVertexNames = sorter.arrange(adjacentVertexNames);

        for (String name : sortedAdjacentVertexNames) {
            ret.append(' ');
            ret.append(name);
            boolean firsttime = true;
            List<Edge> edges = adjacent.get(adjacentVertexNamesToIds.get(name));
            for (Edge e : edges) {
                if (firsttime) {
                    firsttime = false;
                } else {
                    toStringExecutor(ret);
                }
                ret.append(' ');
                ret.append(e.getWeight());
            }
            ret.append(';');
        }
        if (data.hasData()) {
            toStringGateKeeper(ret);
        }
        return ret.toString();
    }

    private void toStringGateKeeper(StringBuilder ret) {
        ret.append(data);
    }

    private void toStringExecutor(StringBuilder ret) {
        ret.append(',');
    }

    private void toStringService(Set<String> adjacentVertexNames, Map<String, Integer> adjacentVertexNamesToIds, Edge edge) {
        String sinkName = edge.getSink().getName();
        int sinkId = edge.getSink().getId();
        adjacentVertexNames.add(sinkName);
        adjacentVertexNamesToIds.put(sinkName, sinkId);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }

        if ((obj == null) || (getClass() != obj.getClass())) {
            return false;
        }

        Vertex vertex = (Vertex) obj;

        return id == vertex.id;
    }

    @Override
    public int hashCode() {
        return id;
    }

    private class VertexEntity {
        private Edge edge;

        public VertexEntity(Edge edge) {
            this.edge = edge;
        }

        public void invoke() {
            removeNeighbor(edge.getSink());
        }
    }
}
