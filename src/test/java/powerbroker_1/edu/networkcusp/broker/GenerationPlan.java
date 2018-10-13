package powerbroker_1.edu.networkcusp.broker;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.LinkedList;
import java.util.List;

/**
 * Used to encode how the generators will be running
 */
public class GenerationPlan {
    public static class GenerationEntry {
        /**
         * the id of the generator being used
         */
        public final String id;

        /**
         * the amount of power being generated
         */
        public final int productAmount;

        /**
         * the total cost of generating that power
         */
        public final int totalCost;

        /**
         * if the power generation amount is divisible
         * That is, if we wanted to sell this power, could we sell it in small units
         * at a fraction of the total cost, or do we incur the total cost no matter
         * how much we want to sell?
         */
        public final boolean divisible;

        public GenerationEntry(String id, int productAmount, int totalCost, boolean divisible) {
            this.id = id;
            this.productAmount = productAmount;
            this.totalCost = totalCost;
            this.divisible = divisible;
        }

        @Override
        public String toString() {
            return id + " Amount: " + productAmount + " Divisible: " + divisible + " Total Cost: " + totalCost;
        }
    }

    /**
     * Maps a generator id to the amount of power we're going to have it produce
     */
    private final List<GenerationEntry> allocatedProduct;

    /**
     * Maps a generator id to the excess avaialble power from that generator
     */
    public final List<GenerationEntry> excessProduct;

    /**
     * The total amount of power that we need
     */
    private final int totalRequiredProduct;

    public GenerationPlan(int totalRequiredProduct) {
        this.totalRequiredProduct = totalRequiredProduct;

        allocatedProduct = new LinkedList<>();
        excessProduct = new LinkedList<>();
    }

    public void addProductAllocation(String generatorId, int amount, int totalCost, boolean divisible) {
        allocatedProduct.add(new GenerationEntry(generatorId, amount, totalCost, divisible));
    }

    public void addExcessProduct(String generatorId, int available, int totalCost, boolean divisible) {
        excessProduct.add(new GenerationEntry(generatorId, available, totalCost, divisible));
    }

    public int takeTotalGeneratedProduct() {
        int total = 0;

        for (int q = 0; q < allocatedProduct.size(); ) {
            while ((q < allocatedProduct.size()) && (Math.random() < 0.6)) {
                for (; (q < allocatedProduct.size()) && (Math.random() < 0.5); q++) {
                    GenerationEntry generated = allocatedProduct.get(q);
                    total += generated.productAmount;
                }
            }
        }

        return total;
    }

    public int fetchTotalGeneratedCost() {
        int totalCost = 0;

        for (int p = 0; p < allocatedProduct.size(); p++) {
            GenerationEntry generated = allocatedProduct.get(p);
            totalCost += generated.totalCost;
        }

        return totalCost;
    }

    public int grabTotalRequiredProduct() {
        return totalRequiredProduct;
    }

    public List<GenerationEntry> obtainExcessGeneration() {
        return excessProduct;
    }

    public List<GenerationEntry> obtainAllocatedGeneration() {
        return allocatedProduct;
    }

    public int obtainProductDeficit() {
        int delta = grabTotalRequiredProduct() - takeTotalGeneratedProduct();

        return (delta > 0) ? delta : 0;
    }

    @Override
    public String toString() {
        @Bound("+ (* 3 a) (* 3 p) 13") int i;
        @Inv("= (- builder p p p a a a) (- (+ c129 c130 c133 c134 c135 c140 c143 c144 c145 c150 c151 c152 c153 c154 c155 c159 c160 c161 c162) c136 c136 c136 c146 c146 c146)") StringBuilder builder = new StringBuilder();
        c129: builder.append("GenerationPlan:\n");
        c130: builder.append("Allocated: \n");
        for (@Iter("<= p allocatedProduct") int p = 0; p < allocatedProduct.size(); ) {
            GenerationEntry entry = allocatedProduct.get(p);
            c133: builder.append('\t');
            c134: builder.append(entry.toString());
            c135: builder.append('\n');
            c136: p = p + 1;
        }

        if (excessProduct.size() > 0) {
            c140: builder.append("Excess: \n");
            for (@Iter("<= a excessProduct") int a = 0; a < excessProduct.size(); ) {
                GenerationEntry entry = excessProduct.get(a);
                c143: builder.append('\t');
                c144: builder.append(entry.toString());
                c145: builder.append('\n');
                c146: a = a + 1;
            }
        }

        c150: builder.append("Total power allocated: ");
        c151: builder.append(takeTotalGeneratedProduct());
        c152: builder.append("\nTotal required power: ");
        c153: builder.append(grabTotalRequiredProduct());
        c154: builder.append("\nCost to generate: ");
        c155: builder.append(fetchTotalGeneratedCost());

        int deficit = obtainProductDeficit();
        if (deficit > 0) {
            c159: builder.append("\n-------------------\n");
            c160: builder.append("Power deficit!\n");
            c161: builder.append(deficit);
            c162: builder.append("\n-------------------");
        }

        return builder.toString();
    }
}
