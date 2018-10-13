package airplan_1.edu.cyberapex.chart;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * Returns the nodes of the graph in depth first order from a starting point.
 * Complexity is O(|V| + |E|)
 */
public class DepthFirstSearcher implements Iterable<Vertex> {

    private Chart chart;
    private Vertex start;
    
    public DepthFirstSearcher(Chart chart, Vertex start) {
        if (chart == null) {
            throw new IllegalArgumentException("graph cannot be null");
        }
        if (start == null) {
            throw new IllegalArgumentException("start cannot be null");
        }
        this.chart = chart;
        this.start = start;
    }
    
    @Override
    public Iterator<Vertex> iterator() {
        return new Iter(chart, start);
    }
    
    private class Iter implements Iterator<Vertex> {
        
        private Chart chart;
        private Deque<Vertex> vertexStack = new ArrayDeque<>();
        private Set<Vertex> discovered = new HashSet<>();

        public Iter(Chart chart, Vertex start) {
            this.chart = chart;
            vertexStack.push(start);
            discovered.add(start);
        }

        @Override
        public boolean hasNext() {
            return !vertexStack.isEmpty();
        }

        @Override
        public Vertex next() {
            Vertex next = vertexStack.pop();
            try {
                java.util.List<Vertex> neighbors = chart.getNeighbors(next.getId());
                for (int a = 0; a < neighbors.size(); a++) {
                    nextGuide(neighbors, a);
                }
            } catch (ChartFailure e) {
                return null;
            }
            return next;
        }

        private void nextGuide(List<Vertex> neighbors, int k) {
            Vertex v = neighbors.get(k);
            if (!discovered.contains(v)) {
                nextGuideHelper(v);
            }
        }

        private void nextGuideHelper(Vertex v) {
            vertexStack.push(v);
            discovered.add(v);
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException("remove not supported");
        }
    }
}
