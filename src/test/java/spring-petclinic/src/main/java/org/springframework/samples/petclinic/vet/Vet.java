/*
 * Copyright 2002-2013 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.springframework.samples.petclinic.vet;

import java.util.*;

import javax.persistence.Entity;
import javax.persistence.FetchType;
import javax.persistence.JoinColumn;
import javax.persistence.JoinTable;
import javax.persistence.ManyToMany;
import javax.persistence.Table;
import javax.xml.bind.annotation.XmlElement;

import org.springframework.beans.support.MutableSortDefinition;
import org.springframework.beans.support.PropertyComparator;
import org.springframework.samples.petclinic.model.Person;
import plv.colorado.edu.quantmchecker.qual.*;

/**
 * Simple JavaBean domain object representing a veterinarian.
 *
 * @author Ken Krebs
 * @author Juergen Hoeller
 * @author Sam Brannen
 * @author Arjen Poutsma
 */
@Entity
@Table(name = "vets")
public class Vet extends Person {

    @ManyToMany(fetch = FetchType.EAGER)
    @JoinTable(name = "vet_specialties", joinColumns = @JoinColumn(name = "vet_id"), inverseJoinColumns = @JoinColumn(name = "specialty_id"))
    private Set<Specialty> specialties;

    protected void setSpecialtiesInternal(Set<Specialty> specialties) {
        this.specialties = specialties;
    }

    @XmlElement
    public List<Specialty> getSpecialties() {
        if (this.specialties == null) {
            this.specialties = new HashSet<>();
        }
        @Bound("specialties") int i;
        @Inv("= (- sortedSpecs it) (- c65 c64)") List<Specialty> sortedSpecs = new ArrayList<>();
        @Iter("<= it specialties") Iterator<Specialty> it = specialties.iterator();
        Specialty s;
        while (it.hasNext()) {
            c64: s = it.next();
            c65: sortedSpecs.add(s);
        }
        PropertyComparator.sort(sortedSpecs,
                new MutableSortDefinition("name", true, true));
        return Collections.unmodifiableList(sortedSpecs);
    }

    public int getNrOfSpecialties() {
        if (this.specialties == null) {
            this.specialties = new HashSet<>();
        }
        return specialties.size();
    }

    @Summary({"this.specialties", "1"})
    public void addSpecialty(Specialty specialty) {
        if (this.specialties == null) {
            this.specialties = new HashSet<>();
        }
        specialties.add(specialty);
    }

}
