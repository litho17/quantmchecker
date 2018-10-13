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
 * <p>
 * A submitter. Corresponds to the SUBMITTER_RECORD structure in the GEDCOM standard.
 * </p>
 * <p>
 * Note that a valid GEDCOM requires at least one Submitter record to be valid.
 * </p>
 * 
 * @author frizbog1
 */
public class Submitter extends AbstractElement {
    /**
     * Serial Version UID
     */
    private static final long serialVersionUID = 964849855689332389L;

    /**
     * The address of this submitter
     */
    private Address address;

    /**
     * The change date for this submitter
     */
    private ChangeDate changeDate;

    /**
     * The emails for this submitter. New for GEDCOM 5.5.1
     */
    private List<StringWithCustomTags> emails = getEmails(Options.isCollectionInitializationEnabled());

    /**
     * Fax numbers. New for GEDCOM 5.5.1.
     */
    private List<StringWithCustomTags> faxNumbers = getFaxNumbers(Options.isCollectionInitializationEnabled());

    /**
     * The language preferences
     */
    private List<StringWithCustomTags> languagePref = getLanguagePref(Options.isCollectionInitializationEnabled());

    /**
     * The multimedia for this submitter
     */
    private List<Multimedia> multimedia = getMultimedia(Options.isCollectionInitializationEnabled());

    /**
     * The name of this submitter
     */
    private StringWithCustomTags name;

    /**
     * Notes about this object
     */
    private List<Note> notes = getNotes(Options.isCollectionInitializationEnabled());

    /**
     * The phone numbers for this submitter
     */
    private List<StringWithCustomTags> phoneNumbers = getPhoneNumbers(Options.isCollectionInitializationEnabled());

    /**
     * The record ID number
     */
    private StringWithCustomTags recIdNumber;

    /**
     * The registration file number for this submitter
     */
    private StringWithCustomTags regFileNumber;

    /**
     * The user references for this submitter
     */
    private List<UserReference> userReferences = getUserReferences(Options.isCollectionInitializationEnabled());

    /**
     * Web URL's. New for GEDCOM 5.5.1.
     */
    private List<StringWithCustomTags> wwwUrls = getWwwUrls(Options.isCollectionInitializationEnabled());

    /**
     * The xref for this submitter
     */
    private String xref;

    /**
     * {@inheritDoc}
     */
    @SuppressWarnings("PMD.ExcessiveMethodLength")
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
        Submitter other = (Submitter) obj;
        if (address == null) {
            if (other.address != null) {
                return false;
            }
        } else if (!address.equals(other.address)) {
            return false;
        }
        if (changeDate == null) {
            if (other.changeDate != null) {
                return false;
            }
        } else if (!changeDate.equals(other.changeDate)) {
            return false;
        }
        if (languagePref == null) {
            if (other.languagePref != null) {
                return false;
            }
        } else if (!languagePref.equals(other.languagePref)) {
            return false;
        }
        if (multimedia == null) {
            if (other.multimedia != null) {
                return false;
            }
        } else if (!multimedia.equals(other.multimedia)) {
            return false;
        }
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        if (notes == null) {
            if (other.notes != null) {
                return false;
            }
        } else if (!notes.equals(other.notes)) {
            return false;
        }
        if (phoneNumbers == null) {
            if (other.phoneNumbers != null) {
                return false;
            }
        } else if (!phoneNumbers.equals(other.phoneNumbers)) {
            return false;
        }
        if (wwwUrls == null) {
            if (other.wwwUrls != null) {
                return false;
            }
        } else if (!wwwUrls.equals(other.wwwUrls)) {
            return false;
        }
        if (faxNumbers == null) {
            if (other.faxNumbers != null) {
                return false;
            }
        } else if (!faxNumbers.equals(other.faxNumbers)) {
            return false;
        }
        if (emails == null) {
            if (other.emails != null) {
                return false;
            }
        } else if (!emails.equals(other.emails)) {
            return false;
        }
        if (recIdNumber == null) {
            if (other.recIdNumber != null) {
                return false;
            }
        } else if (!recIdNumber.equals(other.recIdNumber)) {
            return false;
        }
        if (regFileNumber == null) {
            if (other.regFileNumber != null) {
                return false;
            }
        } else if (!regFileNumber.equals(other.regFileNumber)) {
            return false;
        }
        if (userReferences == null) {
            if (other.userReferences != null) {
                return false;
            }
        } else if (!userReferences.equals(other.userReferences)) {
            return false;
        }
        if (xref == null) {
            if (other.xref != null) {
                return false;
            }
        } else if (!xref.equals(other.xref)) {
            return false;
        }
        return true;
    }

    /**
     * Gets the address.
     *
     * @return the address
     */
    public Address getAddress() {
        return address;
    }

    /**
     * Gets the change date.
     *
     * @return the change date
     */
    public ChangeDate getChangeDate() {
        return changeDate;
    }

    /**
     * Gets the emails.
     *
     * @return the emails
     */
    public List<StringWithCustomTags> getEmails() {
        return emails;
    }

    /**
     * Get the emails
     * 
     * @param initializeIfNeeded
     *            initialize the collection, if needed?
     * @return the emails
     */
    public List<StringWithCustomTags> getEmails(boolean initializeIfNeeded) {
        if (initializeIfNeeded && emails == null) {
            emails = new ArrayList<StringWithCustomTags>(0);
        }

        return emails;
    }

    /**
     * Gets the fax numbers.
     *
     * @return the fax numbers
     */
    public List<StringWithCustomTags> getFaxNumbers() {
        return faxNumbers;
    }

    /**
     * Get the fax numbers
     * 
     * @param initializeIfNeeded
     *            initialize the collection, if needed?
     * @return the fax numbers
     */
    public List<StringWithCustomTags> getFaxNumbers(boolean initializeIfNeeded) {
        if (initializeIfNeeded && faxNumbers == null) {
            faxNumbers = new ArrayList<StringWithCustomTags>(0);
        }
        return faxNumbers;
    }

    /**
     * Gets the language pref.
     *
     * @return the language pref
     */
    public List<StringWithCustomTags> getLanguagePref() {
        return languagePref;
    }

    /**
     * Get the languagePref
     * 
     * @param initializeIfNeeded
     *            initialize the collection, if needed?
     * @return the languagePref
     */
    public List<StringWithCustomTags> getLanguagePref(boolean initializeIfNeeded) {
        if (initializeIfNeeded && languagePref == null) {
            languagePref = new ArrayList<StringWithCustomTags>(0);
        }
        return languagePref;
    }

    /**
     * Gets the multimedia.
     *
     * @return the multimedia
     */
    public List<Multimedia> getMultimedia() {
        return multimedia;
    }

    /**
     * Get the multimedia
     * 
     * @param initializeIfNeeded
     *            initialize the collection, if needed?
     * @return the multimedia
     */
    public List<Multimedia> getMultimedia(boolean initializeIfNeeded) {
        if (initializeIfNeeded && multimedia == null) {
            multimedia = new ArrayList<Multimedia>(0);
        }
        return multimedia;
    }

    /**
     * Gets the name.
     *
     * @return the name
     */
    public StringWithCustomTags getName() {
        return name;
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
     * Gets the phone numbers.
     *
     * @return the phone numbers
     */
    public List<StringWithCustomTags> getPhoneNumbers() {
        return phoneNumbers;
    }

    /**
     * Get the phone numbers
     * 
     * @param initializeIfNeeded
     *            initialize the collection, if needed?
     * @return the phone numbers
     */
    public List<StringWithCustomTags> getPhoneNumbers(boolean initializeIfNeeded) {
        if (initializeIfNeeded && phoneNumbers == null) {
            phoneNumbers = new ArrayList<StringWithCustomTags>(0);
        }
        return phoneNumbers;
    }

    /**
     * Gets the rec id number.
     *
     * @return the rec id number
     */
    public StringWithCustomTags getRecIdNumber() {
        return recIdNumber;
    }

    /**
     * Gets the reg file number.
     *
     * @return the reg file number
     */
    public StringWithCustomTags getRegFileNumber() {
        return regFileNumber;
    }

    /**
     * Gets the user references.
     *
     * @return the user references
     */
    public List<UserReference> getUserReferences() {
        return userReferences;
    }

    /**
     * Get the user references
     * 
     * @param initializeIfNeeded
     *            initialize the collection, if needed?
     * @return the user references
     */
    public List<UserReference> getUserReferences(boolean initializeIfNeeded) {
        if (initializeIfNeeded && userReferences == null) {
            userReferences = new ArrayList<UserReference>(0);
        }
        return userReferences;
    }

    /**
     * Gets the www urls.
     *
     * @return the www urls
     */
    public List<StringWithCustomTags> getWwwUrls() {
        return wwwUrls;
    }

    /**
     * Get the www urls
     * 
     * @param initializeIfNeeded
     *            initialize the collection, if needed?
     * @return the www urls
     */
    public List<StringWithCustomTags> getWwwUrls(boolean initializeIfNeeded) {
        if (initializeIfNeeded && wwwUrls == null) {
            wwwUrls = new ArrayList<StringWithCustomTags>(0);
        }
        return wwwUrls;
    }

    /**
     * Gets the xref.
     *
     * @return the xref
     */
    public String getXref() {
        return xref;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + (address == null ? 0 : address.hashCode());
        result = prime * result + (changeDate == null ? 0 : changeDate.hashCode());
        result = prime * result + (languagePref == null ? 0 : languagePref.hashCode());
        result = prime * result + (multimedia == null ? 0 : multimedia.hashCode());
        result = prime * result + (name == null ? 0 : name.hashCode());
        result = prime * result + (notes == null ? 0 : notes.hashCode());
        result = prime * result + (phoneNumbers == null ? 0 : phoneNumbers.hashCode());
        result = prime * result + (faxNumbers == null ? 0 : faxNumbers.hashCode());
        result = prime * result + (wwwUrls == null ? 0 : wwwUrls.hashCode());
        result = prime * result + (emails == null ? 0 : emails.hashCode());
        result = prime * result + (recIdNumber == null ? 0 : recIdNumber.hashCode());
        result = prime * result + (regFileNumber == null ? 0 : regFileNumber.hashCode());
        result = prime * result + (userReferences == null ? 0 : userReferences.hashCode());
        result = prime * result + (xref == null ? 0 : xref.hashCode());
        return result;
    }

    /**
     * Sets the address.
     *
     * @param address
     *            the new address
     */
    public void setAddress(Address address) {
        this.address = address;
    }

    /**
     * Sets the change date.
     *
     * @param changeDate
     *            the new change date
     */
    public void setChangeDate(ChangeDate changeDate) {
        this.changeDate = changeDate;
    }

    /**
     * Sets the name.
     *
     * @param name
     *            the new name
     */
    public void setName(StringWithCustomTags name) {
        this.name = name;
    }

    /**
     * Sets the rec id number.
     *
     * @param recIdNumber
     *            the new rec id number
     */
    public void setRecIdNumber(StringWithCustomTags recIdNumber) {
        this.recIdNumber = recIdNumber;
    }

    /**
     * Sets the reg file number.
     *
     * @param regFileNumber
     *            the new reg file number
     */
    public void setRegFileNumber(StringWithCustomTags regFileNumber) {
        this.regFileNumber = regFileNumber;
    }

    /**
     * Sets the xref.
     *
     * @param xref
     *            the new xref
     */
    public void setXref(String xref) {
        this.xref = xref;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append("Submitter [");
        if (address != null) {
            builder.append("address=");
            builder.append(address);
            builder.append(", ");
        }
        if (changeDate != null) {
            builder.append("changeDate=");
            builder.append(changeDate);
            builder.append(", ");
        }
        if (emails != null) {
            builder.append("emails=");
            builder.append(emails);
            builder.append(", ");
        }
        if (faxNumbers != null) {
            builder.append("faxNumbers=");
            builder.append(faxNumbers);
            builder.append(", ");
        }
        if (languagePref != null) {
            builder.append("languagePref=");
            builder.append(languagePref);
            builder.append(", ");
        }
        if (multimedia != null) {
            builder.append("multimedia=");
            builder.append(multimedia);
            builder.append(", ");
        }
        if (name != null) {
            builder.append("name=");
            builder.append(name);
            builder.append(", ");
        }
        if (notes != null) {
            builder.append("notes=");
            builder.append(notes);
            builder.append(", ");
        }
        if (phoneNumbers != null) {
            builder.append("phoneNumbers=");
            builder.append(phoneNumbers);
            builder.append(", ");
        }
        if (recIdNumber != null) {
            builder.append("recIdNumber=");
            builder.append(recIdNumber);
            builder.append(", ");
        }
        if (regFileNumber != null) {
            builder.append("regFileNumber=");
            builder.append(regFileNumber);
            builder.append(", ");
        }
        if (userReferences != null) {
            builder.append("userReferences=");
            builder.append(userReferences);
            builder.append(", ");
        }
        if (wwwUrls != null) {
            builder.append("wwwUrls=");
            builder.append(wwwUrls);
            builder.append(", ");
        }
        if (xref != null) {
            builder.append("xref=");
            builder.append(xref);
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
