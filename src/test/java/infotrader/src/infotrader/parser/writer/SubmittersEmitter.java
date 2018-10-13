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
package infotrader.src.infotrader.parser.writer;

import java.util.Collection;

import infotrader.src.infotrader.parser.exception.InfoTraderWriterException;
import infotrader.src.infotrader.parser.exception.WriterCancelledException;
import infotrader.src.infotrader.parser.model.StringWithCustomTags;
import infotrader.src.infotrader.parser.model.Submitter;

/**
 * @author frizbog
 *
 */
class SubmittersEmitter extends AbstractEmitter<Collection<Submitter>> {

    /**
     * Constructor
     * 
     * @param baseWriter
     *            The base Gedcom writer class this Emitter is partnering with to emit the entire file
     * @param startLevel
     *            write starting at this level
     * @param writeFrom
     *            object to write
     * @throws WriterCancelledException
     *             if cancellation was requested during the operation
     */
    SubmittersEmitter(InfoTraderWriter baseWriter, int startLevel, Collection<Submitter> writeFrom) throws WriterCancelledException {
        super(baseWriter, startLevel, writeFrom);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void emit() throws InfoTraderWriterException {
        if (writeFrom == null) {
            return;
        }
        for (Submitter s : writeFrom) {
            emitTag(0, s.getXref(), "SUBM");
            emitTagWithOptionalValueAndCustomSubtags(1, "NAME", s.getName());
            new AddressEmitter(baseWriter, 1, s.getAddress()).emit();
            new MultimediaLinksEmitter(baseWriter, 1, s.getMultimedia()).emit();
            if (s.getLanguagePref() != null) {
                for (StringWithCustomTags l : s.getLanguagePref()) {
                    emitTagWithRequiredValue(1, "LANG", l);
                }
            }
            emitStringsWithCustomTags(1, s.getPhoneNumbers(), "PHON");
            emitStringsWithCustomTags(1, s.getWwwUrls(), "WWW");
            emitStringsWithCustomTags(1, s.getFaxNumbers(), "FAX");
            emitStringsWithCustomTags(1, s.getEmails(), "EMAIL");
            emitTagIfValueNotNull(1, "RFN", s.getRegFileNumber());
            emitTagIfValueNotNull(1, "RIN", s.getRecIdNumber());
            new ChangeDateEmitter(baseWriter, 1, s.getChangeDate()).emit();
            emitCustomTags(1, s.getCustomTags());
        }
    }

}
