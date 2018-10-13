package airplan_1.edu.cyberapex.chart;

import java.io.PrintStream;

/**
 * Prints the nodes in the order provided
 */
public class TraversalPrinter {

    public void print(PrintStream out, Iterable<Vertex> iter) {
        boolean printedOne = false;
        for (Vertex v : iter) {
            if (printedOne) {
                printEngine(out);
            }
            out.print(v.getName());
            printedOne = true;
        }
        out.println();
    }

    private void printEngine(PrintStream out) {
        out.print("->");
    }

}
