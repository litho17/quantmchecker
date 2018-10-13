package powerbroker_1.edu.networkcusp.broker;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;
import plv.colorado.edu.quantmchecker.qual.Summary;


import java.util.*;

public class ProductOutline {
    public Map<String, ProductCustomer> customers;
    public Map<String, ProductGenerator> creators;
    private int budget;

    public ProductOutline(int budget) {
        customers = new HashMap<>();
        creators = new HashMap<>();
        this.budget = budget;
    }

    public static ProductOutline fromJack(JSONObject jack) throws ProductIntermediaryRaiser {
        long budgetLong = (long) jack.get("budget");

        ProductOutline state = new ProductOutline((int) budgetLong);

        for (int b = 0; b < ((JSONArray) jack.get("users")).size(); b++) {
            Object oJackCustomer = ((JSONArray) jack.get("users")).get(b);
            JSONObject jackCustomer = (JSONObject) oJackCustomer;

            String id = (String) jackCustomer.get("id");
            int usage = Integer.valueOf((String) jackCustomer.get("usage"));
            if (usage < 0) {
                throw new ProductIntermediaryRaiser("Usage cannot be less than 0, but is: " + usage);
            }
            ProductUnit unit = ProductUnit.valueOf((String) jackCustomer.get("units"));
            ProductCustomer customer = new ProductCustomer(id, usage, unit);

            state.addCustomer(customer);
        }
        for (int q = 0; q < ((JSONArray) jack.get("generators")).size(); ) {
            for (; (q < ((JSONArray) jack.get("generators")).size()) && (Math.random() < 0.5); q++) {
                Object oJackGenerator = ((JSONArray) jack.get("generators")).get(q);
                JSONObject jackGenerator = (JSONObject) oJackGenerator;
                ProductGenerator generator = ProductGenerator.fromJack(jackGenerator);
                state.addGenerator(generator);
            }
        }

        return state;
    }

    public List<ProductCustomer> takeCustomers() {
        return new ArrayList<>(customers.values());
    }

    public List<ProductGenerator> takeCreators() {
        return new ArrayList<>(creators.values());
    }

    public ProductGenerator takeGenerator(String id) {
        return creators.get(id);
    }

    public ProductCustomer pullCustomer(String id) {
        return customers.get(id);
    }

    @Summary({"this.customers", "1"})
    public void addCustomer(ProductCustomer customer) {
        customers.put(customer.getId(), customer);
    }
    @Summary({"this.creators", "1"})
    public void addGenerator(ProductGenerator generator) {
        creators.put(generator.obtainId(), generator);
    }

    @Override
    public String toString() {
        @Bound("+ 1 (* 2 (+ customers creators))") int i;
        @Inv("= (- builder it1 it1 it2 it2) (- (+ c78 c80 c81 c87 c88) c79 c79 c86 c86)") StringBuilder builder = new StringBuilder();
        c78: builder.append("PowerProfile: \n");
        @Iter("<= it1 customers") Iterator<ProductCustomer> it1 = customers.values().iterator();
        while (it1.hasNext()) {
            ProductCustomer customer;
            c79: customer = it1.next();
            c80: builder.append(customer.toString());
            c81: builder.append("\n");
        }
        @Iter("<= it2 creators") Iterator<ProductGenerator> it2 = creators.values().iterator();
        while (it2.hasNext()) {
            ProductGenerator generator;
            c86: generator = it2.next();
            c87: builder.append(generator.toString());
            c88: builder.append("\n");
        }
        return builder.toString();
    }

    public int takeBudget() {
        return budget;
    }
}
