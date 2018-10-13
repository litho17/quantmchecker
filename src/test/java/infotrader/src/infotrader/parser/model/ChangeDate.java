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
package infotrader.src.infotrader.parser.model;

import java.util.ArrayList;
import java.util.List;

import infotrader.src.infotrader.parser.Options;

/**
 * A date/time that a change was made.
 * 
 * @author frizbog1
 */
public class ChangeDate extends AbstractElement {
    /**
     * Serial Version UID
     */
    private static final long serialVersionUID = 6134688970119877487L;

    /**
     * The date (as a string)
     */
    private StringWithCustomTags date;

    /**
     * Notes about this object
     */
    private List<Note> notes = getNotes(Options.isCollectionInitializationEnabled());

    /**
     * The time (as a string)
     */
    private StringWithCustomTags time;

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        ChangeDate other = (ChangeDate) obj;
        if (date == null) {
            if (other.date != null) {
                return false;
            }
        } else if (!date.equals(other.date)) {
            return false;
        }
        if (notes == null) {
            if (other.notes != null) {
                return false;
            }
        } else if (!notes.equals(other.notes)) {
            return false;
        }
        if (time == null) {
            if (other.time != null) {
                return false;
            }
        } else if (!time.equals(other.time)) {
            return false;
        }
        return true;
    }

    /**
     * Gets the date.
     *
     * @return the date
     */
    public StringWithCustomTags getDate() {
        return date;
    }

    /**
     * Gets the notes.
     *
     * @return the notes
     */
    public List<Note> getNotes() {
        return notes;
    }

    /**
     * Get the notes
     * 
     * @param initializeIfNeeded
     *            initialize the collection if needed?
     * 
     * @return the notes
     */
    public List<Note> getNotes(boolean initializeIfNeeded) {
        if (initializeIfNeeded && notes == null) {
            notes = new ArrayList<Note>(0);
        }
        return notes;
    }

    /**
     * Gets the time.
     *
     * @return the time
     */
    public StringWithCustomTags getTime() {
        return time;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + (date == null ? 0 : date.hashCode());
        result = prime * result + (notes == null ? 0 : notes.hashCode());
        result = prime * result + (time == null ? 0 : time.hashCode());
        return result;
    }

    /**
     * Sets the date.
     *
     * @param date
     *            the new date
     */
    public void setDate(StringWithCustomTags date) {
        this.date = date;
    }

    /**
     * Sets the time.
     *
     * @param time
     *            the new time
     */
    public void setTime(StringWithCustomTags time) {
        this.time = time;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append("ChangeDate [");
        if (date != null) {
            builder.append("date=");
            builder.append(date);
            builder.append(", ");
        }
        if (notes != null) {
            builder.append("notes=");
            builder.append(notes);
            builder.append(", ");
        }
        if (time != null) {
            builder.append("time=");
            builder.append(time);
            builder.append(", ");
        }
        if (customTags != null) {
            builder.append("customTags=");
            builder.append(customTags);
        }
        builder.append("]");
        return builder.toString();
    }
}
