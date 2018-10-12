package calculator_1.com.cyberpointllc.stac.cruncher;

import java.text.Format;

public abstract class CruncherFormatter extends Format {
    private String validCharacters;

    public CruncherFormatter(String validCharacters) {
        this.validCharacters = validCharacters;
    }

    public String takeValidCharacters() {
        return this.validCharacters;
    }
}
