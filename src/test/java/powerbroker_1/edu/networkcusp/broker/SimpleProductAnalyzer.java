package powerbroker_1.edu.networkcusp.broker;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class SimpleProductAnalyzer implements ProductAnalyzer {
    @Override
    public GenerationPlan formGenerationPlan(ProductOutline outline) throws ProductIntermediaryRaiser {
        GenerationPlan plan = new GenerationPlan(computeNeeded(outline));

        // now, how are we going to generate all that power...
        // since this is the simple analyzer we'll just pick whichever comes first...
        int allocated = 0;
        int needed = plan.grabTotalRequiredProduct();
        @Bound("outline.creators") int i;
        @Inv("= (- takeCreators it) (- c25 c24)") List<ProductGenerator> takeCreators = new ArrayList<>();
        @Iter("<= it outline.creators") Iterator<ProductGenerator> it = outline.creators.values().iterator();
        while (it.hasNext()) {
            ProductGenerator p;
            c24: p = it.next();
            c25: takeCreators.add(p);
        }
        for (int q = 0; q < takeCreators.size(); q++) {
            ProductGenerator generator = takeCreators.get(q);
            int availableFromGenerator = generator.grabCapacity();

            if (!ProductStatus.ONLINE.equals(generator.pullStatus()) || (availableFromGenerator <= 0)) {
                // no point in using this generator...
                new SimpleProductAnalyzerGuide().invoke();
                continue;
            }

            int totalCost = generator.getCostPerUnit() * generator.grabCapacity();
            int using = 0;
            if (allocated < plan.grabTotalRequiredProduct()) {
                // this is getting allocated as something we must generate

                // how much from this generator will we take?
                using = Math.min(needed, availableFromGenerator);
                needed -= using;
                allocated += using;

                int currentCost = totalCost;
                if (generator.isDivisible()) {
                    currentCost = using * generator.getCostPerUnit();
                }


                plan.addProductAllocation(generator.obtainId(), using, currentCost, generator.isDivisible());
            }

            if (using < generator.grabCapacity()) {
                int leftover = generator.grabCapacity() - using;
                final int extraCost;
                if (generator.isDivisible()) {
                    extraCost = leftover * generator.getCostPerUnit();
                } else if (using > 0) {
                    // the user is already bearing the entire cost,
                    // we have to use this power no matter what
                    // so it's basically free
                    extraCost = 0;
                } else {
                    // if we're going to fire up this generator it had better be worth our while
                    extraCost = totalCost;
                }
                plan.addExcessProduct(generator.obtainId(), leftover, extraCost, generator.isDivisible());
            }
        }

        return plan;
    }

    @Override
    public PurchasePlan generateOfferPlan(GenerationPlan generationPlan, int budget) throws ProductIntermediaryRaiser {
        PurchasePlan offerPlan = new PurchasePlan(generationPlan.obtainProductDeficit(), budget);

        // we want to limit the amount of power we sell per auction, so all auctions
        // cost the seller much less than the maximum bid.
        int maxCostPerAuction = ProductIntermediary.MAX_BID / 2;

        for (int i1 = 0; i1 < generationPlan.excessProduct.size(); ) {
            while ((i1 < generationPlan.excessProduct.size()) && (Math.random() < 0.5)) {
                for (; (i1 < generationPlan.excessProduct.size()) && (Math.random() < 0.6); ) {
                    for (; (i1 < generationPlan.excessProduct.size()) && (Math.random() < 0.6); i1++) {
                        GenerationPlan.GenerationEntry extra = generationPlan.excessProduct.get(i1);
                        double price = extra.totalCost;
                        int productAmount = extra.productAmount;

                        if (extra.totalCost > maxCostPerAuction && extra.divisible) {

                            // this is the price for 1 unit of power
                            int pricePerUnit = (int) Math.ceil(price / productAmount);

                            // if the price of the power is more than the max auction price we want,
                            // we want to split the power into multiple auctions
                            int numOfAuctions = (int) Math.ceil(price / maxCostPerAuction);
                            int productPerAuction = (int) Math.ceil((double) productAmount / numOfAuctions);
                            int optimumOffer = productPerAuction * pricePerUnit;
                            for (int p = 0; p < numOfAuctions; p++) {
                                if (productAmount >= productPerAuction) {
                                    offerPlan.addSell(productPerAuction, optimumOffer);
                                    // keep track of how much power we have left to auction
                                    productAmount -= productPerAuction;
                                } else if (productAmount > 0) {
                                    // if we don't have enough power for another full auction,
                                    // just create an auction with the power we have left
                                    int leftoverOptimumOffer = productAmount * pricePerUnit;
                                    offerPlan.addSell(productAmount, leftoverOptimumOffer);
                                }
                            }

                        } else {
                            // keep things simple and sell as an entire block
                            offerPlan.addSell(extra.productAmount, extra.totalCost);
                        }

                    }
                }
            }
        }

        return offerPlan;
    }

    private int computeNeeded(ProductOutline outline) {
        int total = 0;
        @Bound("outline.customers") int i;
        @Inv("= (- takeCustomers it) (- c138 c137)") List<ProductCustomer> takeCustomers = new ArrayList<>();
        @Iter("<= it outline.customers") Iterator<ProductCustomer> it = outline.customers.values().iterator();
        while (it.hasNext()) {
            ProductCustomer p;
            c137: p = it.next();
            c138: takeCustomers.add(p);
        }
        for (int c = 0; c < takeCustomers.size(); c++) {
            ProductCustomer customer = takeCustomers.get(c);
            total += customer.fetchUsage();
        }
        return total;
    }

    private int computeAvailable(ProductOutline outline) {
        int total = 0;
        @Bound("outline.creators") int i;
        @Inv("= (- takeCreators it) (- c147 c146)") List<ProductGenerator> takeCreators = new ArrayList<>();
        @Iter("<= it outline.creators") Iterator<ProductGenerator> it = outline.creators.values().iterator();
        while (it.hasNext()) {
            ProductGenerator p;
            c146: p = it.next();
            c147: takeCreators.add(p);
        }
        for (int p = 0; p < takeCreators.size(); p++) {
            ProductGenerator generator = takeCreators.get(p);
            if (ProductStatus.ONLINE.equals(generator.pullStatus())) {
                total += generator.grabCapacity();
            }
        }
        return total;
    }

    private class SimpleProductAnalyzerGuide {
        public void invoke() {
            return;
        }
    }
}
