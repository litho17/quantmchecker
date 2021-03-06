package powerbroker_1.edu.networkcusp.broker;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsIdentity;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsNetworkAddress;
import powerbroker_1.edu.networkcusp.broker.step.StageOverseer;
import powerbroker_1.edu.networkcusp.senderReceivers.ProtocolsNetworkAddressBuilder;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class ProductIntermediary {
    public static final int MAX_BID = 500;
    public static final int MAX_PEERS = 3; // small limit so we can have and verify a bounding box

    private final ProtocolsIdentity identity;
    private final StageOverseer stageOverseer;
    private ProductIntermediaryCustomer productIntermediaryCustomer;

    public ProductIntermediary(ProtocolsIdentity identity) {
        this.identity = identity;
        this.stageOverseer = new StageOverseer(identity, this);
    }

    public void start(File connectionFile, File productFile) throws ProductIntermediaryRaiser {
        // read the power file and create a generation plan
        // we will print the generation to stdout then use the generation plan to create the bid plan
        // we store the bid plan for later use when we want to start auctions
        @InvUnk("Dynamic dispatch") PurchasePlan offerPlan = processFromFile(productFile);

        // read the connection list and start connecting to the other powerbroker instances
        // read the connection list, we expect it to be in the format:
        // <hostname or ip>:<port>
        // <hostname or ip>:<port>
        ProtocolsNetworkAddress us = identity.getCallbackAddress();
        @Bound("+ 1 connectionFile") int i;
        @Inv("= (- peers br) (- c57 c50 c62)") List<ProtocolsNetworkAddress> peers = new ArrayList<>();
        try (@Iter("<= br connectionFile") BufferedReader br = new BufferedReader(new FileReader(connectionFile))) {
            String line;
            int peerCount = 0;
            boolean amIn = false;
            c50: line = br.readLine();
            while (line != null && peerCount < MAX_PEERS) {
                String[] parts = line.split(":");
                if (parts.length != 2) {
                    throw new ProductIntermediaryRaiser("Invalid line: " + line);
                }
                ProtocolsNetworkAddress peer = new ProtocolsNetworkAddressBuilder().setPlace(parts[0]).definePort(Integer.valueOf(parts[1])).formProtocolsNetworkAddress();
                c57: peers.add(peer);
                peerCount++;
                if (peer.equals(us)) {
                    amIn = true;
                }
                c62: line = br.readLine();
            }
            if (!amIn) {
                startEntity();
            }
        } catch (IOException e) {
            throw new ProductIntermediaryRaiser(e);
        }

        // the phaseManager starts the connection phase where connect to others
        // and organize our connections
        stageOverseer.start(peers, us, offerPlan);
    }

    private void startEntity() {
        System.err.println("Connection list contained too many peers.  I am dropping out.");
        System.exit(0);
    }

    private PurchasePlan processFromFile(File file) throws ProductIntermediaryRaiser {
        try {
            // @Bound("+ jack.users jack.generators") int k;
            JSONParser parser = new JSONParser();
            @InvUnk("Extend library class") JSONObject jack = (JSONObject) parser.parse(new FileReader(file));
            // ProductOutline outline = ProductOutline.fromJack(jack);

            long budgetLong = (long) jack.get("budget");

            @Inv("and (= (- state.creators q) (- c104 c105)) (= (- state.customers b) (- c96 c97))") ProductOutline state = new ProductOutline((int) budgetLong);

            JSONArray jackCustomers = (JSONArray) jack.get("users");
            for (@Iter("<= b jack.users") int b = 0; b < jackCustomers.size();) {
                JSONObject oJackCustomer = (JSONObject) jackCustomers.get(b);
                String id = (String) oJackCustomer.get("id");
                int usage = Integer.valueOf((String) oJackCustomer.get("usage"));
                if (usage < 0) {
                    throw new ProductIntermediaryRaiser("Usage cannot be less than 0, but is: " + usage);
                }
                ProductUnit unit = ProductUnit.valueOf((String) oJackCustomer.get("units"));
                ProductCustomer customer = new ProductCustomer(id, usage, unit);
                c96: state.addCustomer(customer);
                c97: b = b + 1;
            }
            JSONArray jackCreators = (JSONArray) jack.get("generators");
            for (@Iter("<= q jack.generators") int q = 0; q < jackCreators.size(); ) {
                for (; (q < jackCreators.size()) && (Math.random() < 0.5);) {
                    Object oJackGenerator = jackCreators.get(q);
                    ProductGenerator generator = ProductGenerator.fromJack((JSONObject) oJackGenerator);
                    c104: state.addGenerator(generator);
                    c105: q = q + 1;
                }
            }


            ProductAnalyzer analyzer = ProductAnalyzerFactory.form();
            GenerationPlan generationPlan = analyzer.formGenerationPlan(state);
            System.out.println(generationPlan);

            @InvUnk("Dynamic dispatch") PurchasePlan offerPlan = analyzer.generateOfferPlan(generationPlan, state.takeBudget());

            System.out.println(offerPlan);

            return offerPlan;
        } catch (IOException e) {
            throw new ProductIntermediaryRaiser(e);
        } catch (@InvUnk("Extend library class") ParseException e) {
            throw new ProductIntermediaryRaiser(e);
        }
    }

    public void stop() {
        stageOverseer.stop();
    }

    public void assignProductIntermediaryCustomer(ProductIntermediaryCustomer productIntermediaryCustomer) {
        this.productIntermediaryCustomer = productIntermediaryCustomer;
    }

    public ProductIntermediaryCustomer getProductIntermediaryCustomer() {
        return productIntermediaryCustomer;
    }

    public ProtocolsIdentity takeIdentity() {
        return identity;
    }
}
