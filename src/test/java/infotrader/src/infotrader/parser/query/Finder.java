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
package infotrader.src.infotrader.parser.query;

import java.util.ArrayList;
import java.util.List;

import infotrader.src.infotrader.parser.model.InfoTrader;


/**
 * A class for finding specific data in a GEDCOM object graph
 * 
 * @author frizbog1
 */
public class Finder {
    /**
     * The gedcom object graph being searched
     */
    private final InfoTrader g;

    /**
     * Constructor. Requires a reference to the { InfoTrader} object being searched.
     * 
     * @param gedcom
     *            the { InfoTrader} object being searched
     */
    public Finder(InfoTrader gedcom) {
        g = gedcom;
    }

    /**
     * Find individuals whose surname and given names match the parameters.
     * 
     * @param surname
     *            the surname of the individual(s) you wish to find. Required, must match exactly (case insensitive).
     * @param given
     *            the given name of the individual(s) you wish to find. Required, must match exactly (case insensitive).
     * @return a { List} of { Individual}s that have both the surname and given name supplied.
     */
    /*public List<Individual> findByName(String surname, String given) {
        return findByName(null, surname, given, null);
    }*/

    /**
     * Find individuals whose surname and given names match the parameters.
     * 
     * @param prefix
     *            the prefix for the name (or null if no prefix)
     * 
     * @param surname
     *            the surname of the individual(s) you wish to find. Required, must match exactly (case insensitive).
     * @param given
     *            the given name of the individual(s) you wish to find. Required, must match exactly (case insensitive).
     * @param suffix
     *            the suffix for the name (or null if no suffix)
     * @return a { List} of { Individual}s that have both the surname and given name supplied.
     */
    /*public List<Individual> findByName(String prefix, String surname, String given, String suffix) {
        List<Individual> result = new ArrayList<Individual>();
        for (Individual i : g.getIndividuals().values()) {
            if (i.getNames() != null) {
                for (PersonalName n : i.getNames()) {
                    // Sometimes the name is broken up into separate fields in the
                    // GEDCOM
                    if ((surname == null || (n.getSurname() != null && surname.equalsIgnoreCase(n.getSurname().getValue()))) && (given == null || (n
                            .getGivenName() != null && given.equalsIgnoreCase(n.getGivenName().getValue())))) {
                        result.add(i);
                        continue;
                    }
                    // Other times they are concatenated with slashes around the
                    // surname
                    StringBuffer lookingFor = new StringBuffer();
                    lookingFor.append(given).append(" /").append(surname).append("/");
                    if (prefix != null) {
                        lookingFor.insert(0, " ").insert(0, prefix);
                    }
                    if (suffix != null) {
                        lookingFor.append(" ").append(suffix);
                    }

                    if (n.getBasic() != null && n.getBasic().equalsIgnoreCase(lookingFor.toString())) {
                        result.add(i);
                        continue;
                    }
                }
            }
        }
        return result;
    }*/
}
