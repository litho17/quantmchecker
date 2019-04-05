package org.springframework.samples.petclinic;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.samples.petclinic.owner.*;
import org.springframework.samples.petclinic.vet.VetController;
import org.springframework.samples.petclinic.vet.VetRepository;
import org.springframework.samples.petclinic.visit.VisitRepository;
import org.springframework.validation.BindingResult;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import org.springframework.ui.ModelMap;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.util.*;

/**
 * @author Tianhan Lu
 */
public class Driver {
    @Autowired
    protected OwnerRepository owners;

    @Autowired
    protected PetRepository pets;

    @Autowired
    protected VisitRepository visits;

    @Autowired
    protected VetRepository vets;

    BindingResult result;

    OwnerRepository clinicService;

    public void main(List<Object> input) throws Exception {
        VetController vetController = new VetController(vets);
        VisitController visitController = new VisitController(visits, pets);
        PetController petController = new PetController(pets, owners);
        OwnerController ownerController = new OwnerController(clinicService);
        @Bound("* 12 input") int i;
        @Inv("= (- model it it it it it) (- (+ c51 c52 c57 c58 c59) c47 c47 c47 c47 c47)") Map<String, Object> model = new HashMap<>();
        @Inv("(and (= (- owner it it it) (- (+ c53 c54 c56) c47 c47 c47)) (= owner.pets 0))") Owner owner = new Owner();
        @Inv("(and (= pet.visits 0) (= pet.owner.pets 0))") Pet pet = new Pet();
        @Inv("= (- modelMap it it it it) (- (+ c53 c54 c55 c56) c47 c47 c47 c47)") ModelMap modelMap = new ModelMap();
        @Iter("<= it input") Iterator<Object> it = input.iterator();
        Object o;
        while (true) {
            c47: o = it.next();
            c51: vetController.showVetList(model);
            c52: visitController.loadPetWithVisit(0, model);
            c53: petController.initCreationForm(owner, modelMap);
            c54: petController.processCreationForm(owner, pet, result, modelMap);
            c55: petController.initUpdateForm(0, modelMap);
            c56: petController.processUpdateForm(pet, result, owner, modelMap);
            c57: ownerController.initCreationForm(model);
            c58: ownerController.initFindForm(model);
            c59: ownerController.processFindForm(owner, result, model);
        }
    }
}
