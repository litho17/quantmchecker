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

import infotrader.src.infotrader.parser.exception.InfoTraderWriterException;
import infotrader.src.infotrader.parser.exception.WriterCancelledException;
import infotrader.src.infotrader.parser.model.Address;

/**
 * An emitter for { Address} objects
 * 
 * @author frizbog
 */
class AddressEmitter extends AbstractEmitter<Address> {

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
    AddressEmitter(InfoTraderWriter baseWriter, int startLevel, Address writeFrom) throws WriterCancelledException {
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
        emitLinesOfText(startLevel, "ADDR", writeFrom.getLines());
        emitTagIfValueNotNull(startLevel + 1, "ADR1", writeFrom.getAddr1());
        emitTagIfValueNotNull(startLevel + 1, "ADR2", writeFrom.getAddr2());
        emitTagIfValueNotNull(startLevel + 1, "CITY", writeFrom.getCity());
        emitTagIfValueNotNull(startLevel + 1, "STAE", writeFrom.getStateProvince());
        emitTagIfValueNotNull(startLevel + 1, "POST", writeFrom.getPostalCode());
        emitTagIfValueNotNull(startLevel + 1, "CTRY", writeFrom.getCountry());
        emitCustomTags(startLevel + 1, writeFrom.getCustomTags());
    }

}
