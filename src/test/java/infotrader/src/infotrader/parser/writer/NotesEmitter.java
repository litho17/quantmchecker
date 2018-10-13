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
import infotrader.src.infotrader.parser.model.Note;
import infotrader.src.infotrader.parser.model.UserReference;

/**
 * Emitter for { Note}s.
 * 
 * @author frizbog
 *
 */
class NotesEmitter extends AbstractEmitter<Collection<Note>> {

    /**
     * Constructor
     * 
     * @param baseWriter
     *            The base Gedcom writer class this Emitter is partnering with to emit the entire file
     * @param startLevel
     *            write starting at this level
     * @param collection
     *            object to write
     * @throws WriterCancelledException
     *             if cancellation was requested during the operation
     */
    NotesEmitter(InfoTraderWriter baseWriter, int startLevel, Collection<Note> collection) throws WriterCancelledException {
        super(baseWriter, startLevel, collection);
    }

    @Override
    protected void emit() throws InfoTraderWriterException {
        if (writeFrom != null) {
            for (Note n : writeFrom) {
                emitNote(startLevel, n);
                emitCustomTags(startLevel + 1, n.getCustomTags());
                if (baseWriter.isCancelled()) {
                    throw new WriterCancelledException("Construction and writing of InfoTrader cancelled");
                }
            }
        }
    }

    /**
     * Emit a note structure (possibly multi-line)
     * 
     * @param level
     *            the level in the hierarchy we are writing at
     * @param note
     *            the note structure
     * @throws InfoTraderWriterException
     *             if the data is malformed and cannot be written
     */
    private void emitNote(int level, Note note) throws InfoTraderWriterException {
        if (level > 0 && note.getXref() != null) {
            emitTagWithRequiredValue(level, "NOTE", note.getXref());
            return;
        }
        emitLinesOfText(level, note.getXref(), "NOTE", note.getLines());
        new SourceCitationEmitter(baseWriter, level + 1, note.getCitations()).emit();
        if (note.getUserReferences() != null) {
            for (UserReference u : note.getUserReferences()) {
                emitTagWithRequiredValue(level + 1, "REFN", u.getReferenceNum());
                emitTagIfValueNotNull(level + 2, "TYPE", u.getType());
            }
        }
        emitTagIfValueNotNull(level + 1, "RIN", note.getRecIdNumber());
        new ChangeDateEmitter(baseWriter, level + 1, note.getChangeDate()).emit();
        emitCustomTags(level + 1, note.getCustomTags());
    }

}
