package textcrunchr_1.com.nicnilov.textmeter;

// import com.cyberpointllc.stac.hashmap.HashMap;

import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.util.HashMap;

public class TextMeter {

    private @Inv("+<self>=+TextMeterProcessor37") HashMap<String, TextLanguage> textLanguages = new  HashMap();

    public TextMeter() {
    }

    @Summary({"textLanguages", "1"})
    public TextLanguage createTextLanguage(final String language) {
        if ((language == null) || (language.length() == 0))
            throw new  IllegalArgumentException();
        TextLanguage tl = new  TextLanguage(language);
        textLanguages.put(language, tl);
        return tl;
    }

    public TextLanguage get(final String language) {
        return textLanguages.get(language);
    }

    public void release(final String language) {
        textLanguages.remove(language);
    }

    public void releaseAll() {
        releaseAllHelper();
    }

    private void releaseAllHelper() {
        textLanguages.clear();
    }
}
