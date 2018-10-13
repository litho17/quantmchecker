package airplan_1.edu.cyberapex.chart;

/**
 * Created by rborbely on 10/13/16.
 */
public class EulerianAlg {

    public static boolean isEulerian(Chart graph) throws ChartFailure {
        ConnectedAlg ca = new ConnectedAlg();
        return ca.isConnected(graph) && !graph.hasOddDegree();
    }
}
