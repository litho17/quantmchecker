/*
 * Copyright (c) 2009-2016 Matthew R. Harrah
 *
 * MIT License
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */
package infotrader.src.infotrader.parser.validate;

import java.util.List;

import infotrader.src.infotrader.parser.Options;
import infotrader.src.infotrader.parser.model.StringWithCustomTags;
import infotrader.src.infotrader.parser.model.Submitter;

/**
 * Validate a { Submitter} object. See { InfoTraderValidator} for usage information.
 * 
 * @author frizbog1
 * 
 */
class SubmitterValidator extends AbstractValidator {

    /**
     * The submitter being validated
     */
    private final Submitter submitter;

    /**
     * Constructor
     * 
     * @param rootValidator
     *            the root validator containing among other things the findings collection
     * @param submitter
     *            the submitter being validated
     */
    public SubmitterValidator(InfoTraderValidator rootValidator, Submitter submitter) {
        this.rootValidator = rootValidator;
        this.submitter = submitter;
    }

    @Override
    protected void validate() {
        if (submitter == null) {
            addError("Submitter being validated is null");
            return;
        }
        checkXref(submitter);
        checkRequiredString(submitter.getName(), "name", submitter);
        checkLanguagePreferences();
        checkOptionalString(submitter.getRecIdNumber(), "record id number", submitter);
        checkOptionalString(submitter.getRegFileNumber(), "submitter registered rfn", submitter);
        if (submitter.getAddress() != null) {
            new AddressValidator(rootValidator, submitter.getAddress()).validate();
        }
        new NotesValidator(rootValidator, submitter, submitter.getNotes()).validate();
    }

    /**
     * Check the language preferences
     */
    private void checkLanguagePreferences() {
        List<StringWithCustomTags> languagePref = submitter.getLanguagePref();
        if (rootValidator.isAutorepairEnabled()) {
            int dups = new DuplicateEliminator<StringWithCustomTags>(languagePref).process();
            if (dups > 0) {
                rootValidator.addInfo(dups + " duplicate language preferences found and removed", submitter);
            }
        }

        if (submitter.getLanguagePref(Options.isCollectionInitializationEnabled()) != null) {
            if (languagePref.size() > 3) {
                addError("Submitter exceeds limit on language preferences (3)", submitter);
            }
            for (StringWithCustomTags s : languagePref) {
                checkRequiredString(s, "language pref", submitter);
            }
        }
    }
}
