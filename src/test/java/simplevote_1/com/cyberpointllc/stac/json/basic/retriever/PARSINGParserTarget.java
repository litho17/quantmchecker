package simplevote_1.com.cyberpointllc.stac.json.basic.retriever;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;

public class PARSINGParserTarget {
    private final PARSINGParser PARSINGParser;

    public PARSINGParserTarget(PARSINGParser PARSINGParser) {
        this.PARSINGParser = PARSINGParser;
    }

    /**
     * Reset the parser to the initial state with a new character reader.
     *
     * @param in - The new character reader.
     * @throws IOException
     * @throws ParseBad
     */
    public void reset(Reader in) {
        PARSINGParser.takeLexer().yyreset(in);
        PARSINGParser.reset();
    }

    /**
     * @return The position of the beginning of the current token.
     */
    public int takePosition() {
        return PARSINGParser.takeLexer().grabPosition();
    }

    public Object parse(String s) throws ParseBad {
        return parse(s, (ContainerFactory) null);
    }

    public Object parse(String s, ContainerFactory containerFactory) throws ParseBad {
        StringReader in = new StringReader(s);
        try {
            return PARSINGParser.parse(in, containerFactory);
        } catch (IOException ie) {
            /*
			 * Actually it will never happen.
			 */
            throw new ParseBad(-1, ParseBad.ERROR_UNEXPECTED_BAD, ie);
        }
    }

    public void parse(Reader in, ContentGuide contentGuide) throws IOException, ParseBad {
        PARSINGParser.parse(in, contentGuide, false);
    }
}