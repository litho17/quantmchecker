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
 * A citation to a repository
 * 
 * @author frizbog1
 */
public class RepositoryCitation extends AbstractElement {

    /**
     * Serial Version UID
     */
    private static final long serialVersionUID = -5547254435002018057L;

    /**
     * Call numbers
     */
    private List<SourceCallNumber> callNumbers = getCallNumbers(Options.isCollectionInitializationEnabled());

    /**
     * Notes about this object
     */
    private List<Note> notes = getNotes(Options.isCollectionInitializationEnabled());

    /**
     * The xref of the repository. Kept as a string copy of the xref deliberately to avoid circular references in the
     * object graph (particularly, Note -&gt; Citation -&gt; Source -&gt; Repository -&gt; Note -&gt; Citation...)
     */
    private String repositoryXref;

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (!(obj instanceof RepositoryCitation)) {
            return false;
        }
        RepositoryCitation other = (RepositoryCitation) obj;
        if (callNumbers == null) {
            if (other.callNumbers != null) {
                return false;
            }
        } else if (!callNumbers.equals(other.callNumbers)) {
            return false;
        }
        if (notes == null) {
            if (other.notes != null) {
                return false;
            }
        } else if (!notes.equals(other.notes)) {
            return false;
        }
        if (repositoryXref == null) {
            if (other.repositoryXref != null) {
                return false;
            }
        } else if (!repositoryXref.equals(other.repositoryXref)) {
            return false;
        }
        return true;
    }

    /**
     * Gets the call numbers.
     *
     * @return the call numbers
     */
    public List<SourceCallNumber> getCallNumbers() {
        return callNumbers;
    }

    /**
     * Get the call numbers
     * 
     * @param initializeIfNeeded
     *            initialize the collection, if needed?
     * @return the call numbers
     */
    public List<SourceCallNumber> getCallNumbers(boolean initializeIfNeeded) {
        if (initializeIfNeeded && callNumbers == null) {
            callNumbers = new ArrayList<SourceCallNumber>(0);
        }
        return callNumbers;
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
     * Gets the repository xref.
     *
     * @return the repository xref
     */
    public String getRepositoryXref() {
        return repositoryXref;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + (callNumbers == null ? 0 : callNumbers.hashCode());
        result = prime * result + (notes == null ? 0 : notes.hashCode());
        result = prime * result + (repositoryXref == null ? 0 : repositoryXref.hashCode());
        return result;
    }

    /**
     * Sets the repository xref.
     *
     * @param repositoryXref
     *            the new repository xref
     */
    public void setRepositoryXref(String repositoryXref) {
        this.repositoryXref = repositoryXref;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append("RepositoryCitation [");
        if (callNumbers != null) {
            builder.append("callNumbers=");
            builder.append(callNumbers);
            builder.append(", ");
        }
        if (notes != null) {
            builder.append("notes=");
            builder.append(notes);
            builder.append(", ");
        }
        if (repositoryXref != null) {
            builder.append("repositoryXref=");
            builder.append(repositoryXref);
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
