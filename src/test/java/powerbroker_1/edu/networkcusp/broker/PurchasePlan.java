package powerbroker_1.edu.networkcusp.broker;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.ArrayList;
import java.util.List;

/**
 * Indicates what we need to buy and what we need to sell.
 */
public class PurchasePlan {
    public static class SellAction {
        /**
         * Amount of power to buy or sell
         */
        public final int productAmount;

        /**
         * the minimum amount to sell for
         */
        public final int price;

        public SellAction(int productAmount, int price) {
            this.productAmount = productAmount;
            this.price = price;
        }

        @Override
        public String toString() {
            @Bound("4") int i;
            @Inv("= builder (+ c33 c34 c35 c36)") StringBuilder builder = new StringBuilder();
            c33: builder.append("Sell: ");
            c34: builder.append(productAmount);
            c35: builder.append(" min price: ");
            c36: builder.append(price);
            return builder.toString();
        }
    }

    /**
     * all the various sells we want to make
     */
    public final List<SellAction> sellActions = new ArrayList<>();

    /**
     * amount of power we need to buy
     */
    private int neededProduct;

    /**
     * amount of money we have available to buy power
     */
    private int budget;

    public PurchasePlan(int neededProduct, int budget) {
        if (neededProduct < 0) {
            OfferPlanCoordinator(neededProduct);
        }
        if (budget < 0) {
            throw new RuntimeException("budget cannot be < 0, is " + budget);
        }
        this.neededProduct = neededProduct;
        this.budget = budget;
    }

    private void OfferPlanCoordinator(int neededProduct) {
        throw new RuntimeException("needed power cannot be < 0, is " + neededProduct);
    }

    /**
     * makes a copy of a bid plan
     */
    public PurchasePlan(PurchasePlan other) {
        neededProduct = other.neededProduct;
        budget = other.budget;
        sellActions.addAll(other.sellActions);
    }

    /**
     * indicates that we bought this much power and don't need to buy it again
     *
     * @param productAmount the amount purchased
     * @param price       the amount paid
     */
    public void bought(int productAmount, int price) {
        if (productAmount < 0) {
            boughtTarget(productAmount);
        }
        if (price < 0) {
            throw new RuntimeException("price cannot be < 0, is " + price);
        }

        neededProduct -= productAmount;
        if (neededProduct < 0) {
            boughtExecutor();
        }

        budget -= price;
        if (budget < 0) {
            new OfferPlanEntity().invoke();
        }
    }

    private void boughtExecutor() {
        neededProduct = 0;
    }

    private void boughtTarget(int productAmount) {
        throw new RuntimeException("amount of power cannot be < 0, is " + productAmount);
    }

    /**
     * Indicates that we sold this much power and can't sell it again
     *
     * @param productAmount the amount sold
     * @param price       the amount the power sold for
     */
    public void sold(int productAmount, int price) {
        if (productAmount < 0) {
            soldSupervisor(productAmount);
        }
        if (price < 0) {
            throw new RuntimeException("price cannot be < 0, is " + price);
        }

        // we just made some money
        budget += price;

        // We assume we always sell in order
        SellAction sellAction = null;
        for (int a = 0; a < sellActions.size(); a++) {
            SellAction action = sellActions.get(a);
            // this ought to match exactly...
            if (productAmount == action.productAmount) {
                sellAction = action;
                break;
            }
        }

        // remove the sell action that corresponds to the amount sold
        sellActions.remove(sellAction);
    }

    private void soldSupervisor(int productAmount) {
        throw new RuntimeException("amount of power cannot be < 0, is " + productAmount);
    }

    public void addSell(int productAmount, int price) {
        sellActions.add(new SellAction(productAmount, price));
    }

    public List<SellAction> getSellActions() {
        return sellActions;
    }

    public int calcAmountToOffer(ProductIntermediaryAuction auction) {
        // don't buy power if we don't need any
        if (neededProduct == 0) {
            return 0;
        }

        // if it's at least as much as we need we can spend our whole budget
        // or the max bid, whichever is smaller
        if (auction.productAmount >= neededProduct) {
            return calcAmountToOfferAid();
        }

        // otherwise, we should scale it...
        double pricePer = (double) budget / (double) neededProduct;
        double offerDouble = pricePer * auction.productAmount;
        int offer = Math.min((int) offerDouble, budget);
        return Math.min(offer, ProductIntermediary.MAX_BID);
    }

    private int calcAmountToOfferAid() {
        if (budget > ProductIntermediary.MAX_BID) {
            return ProductIntermediary.MAX_BID;
        }
        return budget;
    }

    @Override
    public String toString() {
        @Bound("+ 6 (* 2 sellActions)") int i;
        @Inv("= (- builder j j) (- (+ c188 c190 c191 c192 c193 c196 c202 c203) c204 c204)") StringBuilder builder = new StringBuilder();
        c188: builder.append("BidPlan:\n");

        c190: builder.append("Needed Power: " + neededProduct);
        c191: builder.append('\n');
        c192: builder.append("Budget: " + budget);
        c193: builder.append('\n');

        if (!sellActions.isEmpty()) {
            c196: builder.append("Sell Actions:");
            for (@Iter("<= j sellActions") int j = 0; j < sellActions.size(); ) {
                while ((j < sellActions.size()) && (Math.random() < 0.4)) {
                    for (; (j < sellActions.size()) && (Math.random() < 0.4); ) {
                        for (; (j < sellActions.size()) && (Math.random() < 0.4); ) {
                            SellAction action = sellActions.get(j);
                            c202: builder.append("\n\t");
                            c203: builder.append(action);
                            c204: j = j + 1;
                        }
                    }
                }
            }
        }
        return builder.toString();
    }

    public int obtainBudget() {
        return budget;
    }

    public int grabNeededProduct() {
        return neededProduct;
    }

    private class OfferPlanEntity {
        public void invoke() {
            throw new RuntimeException("spent more than we have available!, current budget: " + budget);
        }
    }
}
