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

import infotrader.src.infotrader.parser.model.SourceData;
import infotrader.src.infotrader.parser.model.RepositoryCitation;
import infotrader.src.infotrader.parser.model.SourceCallNumber;
import infotrader.src.infotrader.parser.model.EventRecorded;
import infotrader.src.infotrader.parser.model.Multimedia;
import infotrader.src.infotrader.parser.model.Source;
import java.util.List;

import infotrader.src.infotrader.parser.Options;

/**
 * A validator for { Source} objects. See { InfoTraderValidator} for usage information.
 * 
 * @author frizbog1
 * 
 */
class SourceValidator extends AbstractValidator {

    /**
     * The source being validated
     */
    private final Source source;

    /**
     * Constructor
     * 
     * @param rootValidator
     *            the root validator
     * @param source
     *            the source being validated
     */
    public SourceValidator(InfoTraderValidator rootValidator, Source source) {
        this.rootValidator = rootValidator;
        this.source = source;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void validate() {
        if (source == null) {
            addError("Source is null and cannot be validated");
            return;
        }
        checkXref(source);
        checkChangeDate(source.getChangeDate(), source);
        if (source.getData() != null) {
            SourceData sd = source.getData();
            new NotesValidator(rootValidator, sd, sd.getNotes()).validate();
            checkOptionalString(sd.getRespAgency(), "responsible agency", sd);
            List<EventRecorded> eventsRecorded = sd.getEventsRecorded();
            if (eventsRecorded == null) {
                if (rootValidator.isAutorepairEnabled()) {
                    sd.getEventsRecorded(true).clear();
                    addInfo("Collection of recorded events in source data structure was null - autorepaired", sd);
                } else {
                    addError("Collection of recorded events in source data structure is null", sd);
                }
            } else {
                if (rootValidator.isAutorepairEnabled()) {
                    int dups = new DuplicateEliminator<EventRecorded>(eventsRecorded).process();
                    if (dups > 0) {
                        rootValidator.addInfo(dups + " duplicate recorded events found and removed", sd);
                    }
                }

                for (EventRecorded er : eventsRecorded) {
                    checkOptionalString(er.getDatePeriod(), "date period", er);
                    checkOptionalString(er.getEventType(), "event type", er);
                    checkOptionalString(er.getJurisdiction(), "jurisdiction", er);
                }
            }
        }
        List<Multimedia> multimedia = source.getMultimedia();
        if (multimedia == null && Options.isCollectionInitializationEnabled()) {
            if (rootValidator.isAutorepairEnabled()) {
                source.getMultimedia(true).clear();
                addInfo("Multimedia collection on source was null - autorepaired", source);
            }
            addError("Multimedia collection on source is null", source);
        } else {
            if (rootValidator.isAutorepairEnabled()) {
                int dups = new DuplicateEliminator<Multimedia>(multimedia).process();
                if (dups > 0) {
                    rootValidator.addInfo(dups + " duplicate multimedia found and removed", source);
                }
            }

            if (multimedia != null) {
                for (Multimedia mm : multimedia) {
                    new MultimediaValidator(rootValidator, mm).validate();
                }
            }
        }
        new NotesValidator(rootValidator, source, source.getNotes()).validate();
        checkStringList(source.getOriginatorsAuthors(), "originators/authors", false);
        checkStringList(source.getPublicationFacts(), "publication facts", false);
        checkOptionalString(source.getRecIdNumber(), "automated record id", source);
        checkStringList(source.getSourceText(), "source text", true);
        checkOptionalString(source.getSourceFiledBy(), "source filed by", source);
        checkStringList(source.getTitle(), "title", true);
        checkUserReferences(source.getUserReferences(), source);

        RepositoryCitation c = source.getRepositoryCitation();
        if (c != null) {
            new NotesValidator(rootValidator, c, c.getNotes()).validate();
            checkRequiredString(c.getRepositoryXref(), "repository xref", c);
            checkCallNumbers(c);
        }
    }

    /**
     * Check the call numbers on a RepositoryCitation object
     * 
     * @param citation
     *            the citation to check the call numbers on
     */
    private void checkCallNumbers(RepositoryCitation citation) {
        List<SourceCallNumber> callNumbers = citation.getCallNumbers();
        if (callNumbers == null && Options.isCollectionInitializationEnabled()) {
            if (rootValidator.isAutorepairEnabled()) {
                citation.getCallNumbers(true).clear();
                addInfo("Call numbers collection on repository citation was null - autorepaired", citation);
            } else {
                addError("Call numbers collection on repository citation is null", citation);
            }
        } else {
            if (rootValidator.isAutorepairEnabled()) {
                int dups = new DuplicateEliminator<SourceCallNumber>(callNumbers).process();
                if (dups > 0) {
                    rootValidator.addInfo(dups + " duplicate source call numbers found and removed", citation);
                }
            }
            if (callNumbers != null) {
                for (SourceCallNumber scn : callNumbers) {
                    checkOptionalString(scn.getCallNumber(), "call number", scn);
                    if (scn.getCallNumber() == null) {
                        if (scn.getMediaType() != null) {
                            addError("You cannot specify media type without a call number in a SourceCallNumber structure", scn);
                        }
                    } else {
                        checkOptionalString(scn.getMediaType(), "media type", scn);
                    }
                }
            }
        }
    }
}
