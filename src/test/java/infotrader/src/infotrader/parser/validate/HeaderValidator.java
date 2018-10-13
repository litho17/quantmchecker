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

import infotrader.src.infotrader.parser.model.Corporation;
import infotrader.src.infotrader.parser.model.HeaderSourceData;
import infotrader.src.infotrader.parser.model.SourceSystem;
import infotrader.src.infotrader.parser.model.CharacterSet;
import infotrader.src.infotrader.parser.model.SupportedVersion;
import infotrader.src.infotrader.parser.model.StringWithCustomTags;
import infotrader.src.infotrader.parser.model.InfoTraderVersion;
import infotrader.src.infotrader.parser.model.Header;
import infotrader.src.infotrader.parser.Options;
import infotrader.src.infotrader.parser.io.encoding.Encoding;

/**
 * Validator for a { Header}. See { InfoTraderValidator} for usage information.
 * 
 * @author frizbog1
 * 
 */
class HeaderValidator extends AbstractValidator {

    /**
     * The { Header} being validated
     */
    private final Header header;

    /**
     * Constructor.
     * 
     * @param gedcomValidator
     *            the main validator
     * @param header
     *            the { Header} being validated
     */
    public HeaderValidator(InfoTraderValidator gedcomValidator, Header header) {
        rootValidator = gedcomValidator;
        this.header = header;
    }

    /**
     * Validate the { Header}
     * 
     * @see org.gedcom4j.validate.AbstractValidator#validate()
     */
    @Override
    protected void validate() {
        checkCharacterSet();
        if (header.getCopyrightData() == null && Options.isCollectionInitializationEnabled()) {
            if (rootValidator.isAutorepairEnabled()) {
                header.getCopyrightData(true).clear();
                rootValidator.addInfo("Copyright data collection was null - repaired", header);
            } else {
                rootValidator.addError("Copyright data collection is null - must be at least an empty collection", header);
            }
        }
        checkCustomTags(header);
        checkOptionalString(header.getDate(), "date", header);
        checkOptionalString(header.getDestinationSystem(), "destination system", header);
        /*
         * Filename is actually a required field -- but since the writer automatically fills in the filename if it's
         * blank, treating it as optional here
         */
        checkOptionalString(header.getFileName(), "filename", header);
        if (header.getInfoTraderVersion() == null) {
            if (rootValidator.isAutorepairEnabled()) {
                header.setInfoTraderVersion(new InfoTraderVersion());
                rootValidator.addInfo("InfoTrader version in header was null - repaired", header);
            } else {
                rootValidator.addError("InfoTrader version in header must be specified", header);
                return;
            }
        }
        if (header.getInfoTraderVersion().getVersionNumber() == null) {
            if (rootValidator.isAutorepairEnabled()) {
                header.getInfoTraderVersion().setVersionNumber(SupportedVersion.V5_5_1);
                rootValidator.addInfo("InfoTrader version number in header was null - repaired", header);
            } else {
                rootValidator.addError("InfoTrader version number in header must be specified", header);
                return;
            }
        }
        checkCustomTags(header.getInfoTraderVersion());
        checkOptionalString(header.getLanguage(), "language", header);
        new NotesValidator(rootValidator, header, header.getNotes()).validate();
        checkOptionalString(header.getPlaceHierarchy(), "place hierarchy", header);
        checkSourceSystem();
        if (header.getSubmitter() == null) {
            if (rootValidator.isAutorepairEnabled()) {
                if (rootValidator.gedcom.getSubmitters() == null || rootValidator.gedcom.getSubmitters().isEmpty()) {
                    rootValidator.addError("Submitter not specified in header, and autorepair could not " + "find a submitter to select as default", header);
                } else {
                    // Take the first submitter from the collection and set that
                    // as the primary submitter in the header
                    header.setSubmitter(rootValidator.gedcom.getSubmitters().values().iterator().next());
                }
            } else {
                rootValidator.addError("Submitter not specified in header", header);
            }
            return;
        }
        new SubmitterValidator(rootValidator, header.getSubmitter()).validate();
        if (header.getSubmission() != null) {
            rootValidator.validateSubmission(header.getSubmission());
        }
        checkOptionalString(header.getTime(), "time", header);
    }

    /**
     * Check the character set
     */
    private void checkCharacterSet() {
        if (header.getCharacterSet() == null) {
            if (rootValidator.isAutorepairEnabled()) {
                header.setCharacterSet(new CharacterSet());
                rootValidator.addInfo("Header did not have a character set defined - corrected.", header);
            } else {
                rootValidator.addError("Header has no character set defined", header);
                return;
            }
        }
        if (header.getCharacterSet().getCharacterSetName() == null) {
            if (rootValidator.isAutorepairEnabled()) {
                header.getCharacterSet().setCharacterSetName(new StringWithCustomTags("ANSEL"));
                rootValidator.addInfo("Character set name was not defined", header.getCharacterSet());
            } else {
                rootValidator.addError("Character set name was not defined", header.getCharacterSet());
                return;
            }
        }
        if (!Encoding.isValidCharacterSetName(header.getCharacterSet().getCharacterSetName().getValue())) {
            rootValidator.addError("Character set name is not one of the supported encodings (" + Encoding.getSupportedCharacterSetNames() + ")", header
                    .getCharacterSet().getCharacterSetName());
        }
        checkOptionalString(header.getCharacterSet().getCharacterSetName(), "character set name", header.getCharacterSet());
        checkOptionalString(header.getCharacterSet().getVersionNum(), "character set version number", header.getCharacterSet());
        checkCustomTags(header.getCharacterSet());
    }

    /**
     * Check the source system
     */
    private void checkSourceSystem() {
        SourceSystem ss = header.getSourceSystem();
        if (ss == null) {
            if (rootValidator.isAutorepairEnabled()) {
                ss = new SourceSystem();
                header.setSourceSystem(ss);
                rootValidator.addInfo("No source system specified in header - repaired", header);
            } else {
                rootValidator.addError("No source system specified in header", header);
                return;
            }
        }
        checkCustomTags(ss);
        if (ss.getCorporation() != null) {
            Corporation c = ss.getCorporation();
            checkCustomTags(c);
            if (c.getAddress() != null) {
                new AddressValidator(rootValidator, c.getAddress()).validate();
            }
            if (c.getBusinessName() == null || c.getBusinessName().trim().length() == 0) {
                if (rootValidator.isAutorepairEnabled()) {
                    c.setBusinessName("UNSPECIFIED");
                    rootValidator.addInfo("Corporation for source system exists but had no name - repaired", c);
                } else {
                    rootValidator.addError("Corporation for source system exists but has no name", c);
                }
            }
        }
        checkOptionalString(ss.getProductName(), "product name", ss);
        if (ss.getSourceData() != null) {
            HeaderSourceData sd = ss.getSourceData();
            if (sd.getName() == null || sd.getName().trim().length() == 0) {
                if (rootValidator.isAutorepairEnabled()) {
                    sd.setName("UNSPECIFIED");
                    rootValidator.addInfo("Source data was specified for source system, " + "but name of source data was not specified - repaired", sd);
                } else {
                    rootValidator.addError("Source data is specified for source system, " + "but name of source data is not specified", sd);
                }

            }
            checkOptionalString(sd.getCopyright(), "copyright", sd);
            checkOptionalString(sd.getPublishDate(), "publish date", sd);
            checkCustomTags(sd);
        }
        if (ss.getSystemId() == null) {
            if (rootValidator.isAutorepairEnabled()) {
                ss.setSystemId("UNSPECIFIED");
                rootValidator.addInfo("System ID was not specified in source system in header - repaired", ss);
            } else {
                rootValidator.addError("System ID must be specified in source system in header", ss);
            }
        }
        checkOptionalString(ss.getVersionNum(), "source system version number", ss);
    }
}
