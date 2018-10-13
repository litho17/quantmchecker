package simplevote_1.com.cyberpointllc.stac.json.basic.retriever;

public class PARSINGParserTargetCreator {
    private PARSINGParser parsingParser;

    public PARSINGParserTargetCreator definePARSINGParser(PARSINGParser parsingParser) {
        this.parsingParser = parsingParser;
        return this;
    }

    public PARSINGParserTarget formPARSINGParserTarget() {
        return new PARSINGParserTarget(parsingParser);
    }
}