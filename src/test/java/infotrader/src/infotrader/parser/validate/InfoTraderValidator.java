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

import infotrader.src.infotrader.parser.model.Submission;
import infotrader.src.infotrader.parser.model.StringWithCustomTags;
import infotrader.src.infotrader.parser.model.Repository;
import infotrader.src.infotrader.parser.model.Trailer;
import infotrader.src.infotrader.parser.model.Header;
import infotrader.src.infotrader.parser.model.Submitter;
import infotrader.src.infotrader.parser.model.Note;
import infotrader.src.infotrader.parser.model.Multimedia;
import infotrader.src.infotrader.parser.model.InfoTrader;
import infotrader.src.infotrader.parser.model.Source;
import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import infotrader.src.infotrader.parser.Options;

/**
 * <p>
 * A class to validate the contents of a { InfoTrader} structure. It is used primarily for those users who wish to
 * create and write GEDCOM files, and is of little importance or use to those who wish only to read/parse GEDCOM files
 * and use their data. Validation is performed automatically prior to writing a GEDCOM file by default (although this
 * can be disabled), and there is support for automatically repairing ("autorepair") issues found.
 * </p>
 * <p>
 * <b>Note that the validation framework is a work in progress and as such, is incompletely implemented at this
 * time.</b>
 * </p>
 * <p>
 * General usage is as follows:
 * </p>
 * <ol>
 * <li>Instantiate a { InfoTraderValidator}, passing the { InfoTrader} structure to be validated as the argument to
 * the constructor</li>
 * <li>If desired, turn off automatic repairs during validation by setting { GedcomValidator#autorepairEnabled} to
 * <tt>false</tt>.
 * <li>Call the { GedcomValidator#validate()} method.</li>
 * <li>Inspect the { GedcomValidator#findings} list, which contains { InfoTraderValidationFinding} objects
 * describing the problems that were found. These will include errors that were fixed by autorepair (with severity of
 * INFO), and those that could not be autorepaired (with severity of ERROR or WARNING).</li>
 * </ol>
 * <p>
 * Note again that by default, validation is performed automatically by the { org.gedcom4j.writer.GedcomWriter}
 * class when writing a GEDCOM file out.
 * </p>
 * 
 * <h2>Autorepair</h2>
 * <p>
 * The validation framework, by default and unless disabled, will attempt to automatically repair ("autorepair")
 * problems it finds in the object graph, so that if written as a GEDCOM file, the file written will conform to the
 * GEDCOM spec, as well as to help the developer avoid NullPointerExceptions due to certain items not being instantiated
 * (if they have so selected in the { Options} class.
 * </p>
 * 
 * 
 * @author frizbog1
 */
public class InfoTraderValidator extends AbstractValidator {

    /**
     * Will the most simple, obvious, non-destructive errors be automatically fixed? This includes things like creating
     * empty collections where one is expected but only a null reference exists.
     */
    private boolean autorepairEnabled = true;

    /**
     * The findings from validation
     */
    private final List<InfoTraderValidationFinding> findings = new ArrayList<InfoTraderValidationFinding>();

    /**
     * The gedcom structure being validated
     */
    protected InfoTrader gedcom = null;

    /**
     * Constructor
     * 
     * @param gedcom
     *            the gedcom structure being validated
     */
    public InfoTraderValidator(InfoTrader gedcom) {
        this.gedcom = gedcom;
        rootValidator = this;
    }

    /**
     * Get the findings
     * 
     * @return the findings
     */
    public List<InfoTraderValidationFinding> getFindings() {
        return findings;
    }

    /**
     * Are there any errors in the findings (so far)?
     * 
     * @return true if there exists at least one finding with severity ERROR
     */
    public boolean hasErrors() {
        for (InfoTraderValidationFinding finding : rootValidator.findings) {
            if (finding.getSeverity() == Severity.ERROR) {
                return true;
            }
        }
        return false;
    }

    /**
     * Are there any INFO level items in the findings (so far)?
     * 
     * @return true if there exists at least one finding with severity INFO
     */
    public boolean hasInfo() {
        for (InfoTraderValidationFinding finding : rootValidator.findings) {
            if (finding.getSeverity() == Severity.INFO) {
                return true;
            }
        }
        return false;
    }

    /**
     * Are there any warnings in the findings (so far)?
     * 
     * @return true if there exists at least one finding with severity WARNING
     */
    public boolean hasWarnings() {
        for (InfoTraderValidationFinding finding : rootValidator.findings) {
            if (finding.getSeverity() == Severity.WARNING) {
                return true;
            }
        }
        return false;
    }

    /**
     * Get the autorepair
     * 
     * @return the autorepair
     */
    public boolean isAutorepairEnabled() {
        return autorepairEnabled;
    }

    /**
     * Set the autorepair
     * 
     * @param autorepair
     *            the autorepair to set
     */
    public void setAutorepairEnabled(boolean autorepair) {
        autorepairEnabled = autorepair;
    }

    /**
     * Validate the gedcom file
     */
    @Override
    public void validate() {
        findings.clear();
        if (gedcom == null) {
            addError("InfoTrader structure is null");
            return;
        }
        validateSubmitters();
        validateHeader();

        validateRepositories();
        validateMultimedia();
        validateNotes();
        validateSources();
        validateSubmission(gedcom.getSubmission());
        validateTrailer();
        new NotesValidator(rootValidator, gedcom, new ArrayList<Note>(gedcom.getNotes().values())).validate();
    }

    /**
     * Validate the submission substructure under the root gedcom
     * 
     * @param s
     *            the submission substructure to be validated
     */
    void validateSubmission(Submission s) {

        if (s == null) {
            addError("Submission record on root InfoTrader is null", gedcom);
            return;
        }
        checkXref(s);
        checkOptionalString(s.getAncestorsCount(), "Ancestor count", s);
        checkOptionalString(s.getDescendantsCount(), "Descendant count", s);
        checkOptionalString(s.getNameOfFamilyFile(), "Name of family file", s);
        checkOptionalString(s.getOrdinanceProcessFlag(), "Ordinance process flag", s);
        checkOptionalString(s.getRecIdNumber(), "Automated record id", s);
        checkOptionalString(s.getTempleCode(), "Temple code", s);
    }


    /**
     * Validate the { Gedcom#header} object
     */
    private void validateHeader() {
        if (gedcom.getHeader() == null) {
            if (autorepairEnabled) {
                gedcom.setHeader(new Header());
                addInfo("Header was null - autorepaired");
            } else {
                addError("InfoTrader Header is null");
                return;
            }
        }
        new HeaderValidator(rootValidator, gedcom.getHeader()).validate();
    }


    /**
     * Validate the collection of { Multimedia} objects
     */
    private void validateMultimedia() {
        if (gedcom.getMultimedia() != null) {
            for (Multimedia m : gedcom.getMultimedia().values()) {
                MultimediaValidator mv = new MultimediaValidator(this, m);
                mv.validate();
            }
        }
    }

    /**
     * Validates the notes
     */
    private void validateNotes() {
        int i = 0;
        for (Note n : gedcom.getNotes().values()) {
            i++;
            new NoteValidator(rootValidator, i, n).validate();
        }
    }

    /**
     * Validate the repositories collection
     */
    private void validateRepositories() {
        for (Entry<String, Repository> e : gedcom.getRepositories().entrySet()) {
            if (e.getKey() == null) {
                addError("Entry in repositories collection has null key", e);
                return;
            }
            if (e.getValue() == null) {
                addError("Entry in repositories collection has null value", e);
                return;
            }
            if (!e.getKey().equals(e.getValue().getXref())) {
                addError("Entry in repositories collection is not keyed by the Repository's xref", e);
                return;
            }
            new RepositoryValidator(rootValidator, e.getValue()).validate();
        }

    }

    /**
     * Validate the { Gedcom#sources} collection
     */
    private void validateSources() {
        for (Entry<String, Source> e : gedcom.getSources().entrySet()) {
            if (e.getKey() == null) {
                addError("Entry in sources collection has null key", e);
                return;
            }
            if (e.getValue() == null) {
                addError("Entry in sources collection has null value", e);
                return;
            }
            if (!e.getKey().equals(e.getValue().getXref())) {
                addError("Entry in sources collection is not keyed by the individual's xref", e);
                return;
            }
            new SourceValidator(rootValidator, e.getValue()).validate();
        }
    }

    /**
     * Validate the submitters collection
     */
    private void validateSubmitters() {
        if (gedcom.getSubmitters().isEmpty()) {
            if (autorepairEnabled) {
                Submitter s = new Submitter();
                s.setXref("@SUBM0000@");
                s.setName(new StringWithCustomTags("UNSPECIFIED"));
                gedcom.getSubmitters().put(s.getXref(), s);
                addInfo("Submitters collection was empty - repaired", gedcom);
            } else {
                addError("Submitters collection is empty", gedcom);
            }
        }
        for (Submitter s : gedcom.getSubmitters().values()) {
            new SubmitterValidator(rootValidator, s).validate();
        }
    }

    /**
     * Validate the trailer
     */
    private void validateTrailer() {
        if (gedcom.getTrailer() == null) {
            if (rootValidator.autorepairEnabled) {
                gedcom.setTrailer(new Trailer());
                rootValidator.addInfo("InfoTrader had no trailer - repaired", gedcom);
            } else {
                rootValidator.addError("InfoTrader has no trailer", gedcom);
            }
        }
    }
}
