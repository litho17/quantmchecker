package simplevote_1.com.cyberpointllc.stac.host;

import simplevote_1.com.cyberpointllc.stac.DESHelper;
import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKeyCreator;
import simplevote_1.com.cyberpointllc.stac.basicvote.Reply;
import simplevote_1.com.cyberpointllc.stac.basicvote.Ballot;
import simplevote_1.com.cyberpointllc.stac.basicvote.Choice;
import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import simplevote_1.com.cyberpointllc.stac.basicvote.Issue;
import simplevote_1.com.cyberpointllc.stac.basicvote.PermissionKey;
import simplevote_1.com.cyberpointllc.stac.basicvote.StorageService;
import simplevote_1.com.cyberpointllc.stac.basicvote.Voter;
import simplevote_1.com.cyberpointllc.stac.json.basic.retriever.ParseBad;
import org.apache.commons.lang3.text.WordUtils;
import simplevote_1.com.cyberpointllc.stac.json.basic.PARSINGArray;
import simplevote_1.com.cyberpointllc.stac.json.basic.PARSINGObject;
import simplevote_1.com.cyberpointllc.stac.json.basic.retriever.PARSINGParser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class DirectVoteLoader {
    private static final String BALLOT_TRAIL = "/content/ballots";
    private static final String SURVEY_TRAIL = "/content/elections";
    private static final String VOTER_TRAIL = "/content/voters.json";
    private static final String PERMISSION_KEY_TRAIL = "/content/registrationkeys.json";

    public static void populate(StorageService storageService, String passwordKey, File dataDirectory) throws IOException {
        loadSurveys(new File(dataDirectory.getAbsolutePath() + SURVEY_TRAIL), storageService);
        loadBallots(new File(dataDirectory.getAbsolutePath() + BALLOT_TRAIL), storageService, passwordKey);
        loadPermissionKeys(new File(dataDirectory.getAbsolutePath() + PERMISSION_KEY_TRAIL), storageService);
        loadVoters(new File(dataDirectory.getAbsolutePath() + VOTER_TRAIL), storageService, passwordKey);
        assignDynamicProperties(storageService);
        
        storageService.commit();

        System.out.println(storageService.summary());
    }

    private static void loadBallots(File dataDirectory, StorageService storageService, String passwordKey) {
        File[] fileList = dataDirectory.listFiles();
        if (fileList != null) {
            for (int b = 0; b < fileList.length; b++) {
                File file = fileList[b];
                if (file.isDirectory()) {
                    loadBallots(file, storageService, passwordKey);
                } else {
                    loadBallot(file, storageService);
                }
            }
        }
    }

    private static void loadSurveys(File dataDirectory, StorageService storageService) {
        File[] fileList = dataDirectory.listFiles();
        if (fileList != null) {
            for (int p = 0; p < fileList.length; p++) {
                loadSurveysCoordinator(storageService, fileList[p]);
            }
        }
    }

    private static void loadSurveysCoordinator(StorageService storageService, File file1) {
        File file = file1;
        if (file.isDirectory()) {
            loadSurveys(file, storageService);
        } else {
            loadSurvey(file, storageService);
        }
    }

    private static void loadVoters(File voterFile, StorageService storageService, String passwordKey) {
        try (Reader reader = new FileReader(voterFile)) {
            PARSINGArray voterArray = (PARSINGArray) new PARSINGParser().parse(reader);
            for (int c = 0; c < voterArray.size(); c++) {
                Object voterObj = voterArray.get(c);
                PARSINGObject voter = (PARSINGObject) voterObj;

                String voterId = (String) voter.get("voterId");
                String username = (String) voter.get("username");
                String password = (String) voter.get("password");
                String encryptedPw;
                if (passwordKey != null) {
                    encryptedPw = DESHelper.grabEncryptedString(password, passwordKey);
                } else {
                    encryptedPw = password;
                }

                String name = (String) voter.get("name");

                PARSINGObject traitsPARSING = (PARSINGObject) voter.get("traits");
                Map<String, String> voterTraits = new LinkedHashMap<>();
                for (Object objKey : traitsPARSING.keySet()) {
                    String key = (String) objKey;
                    voterTraits.put(key, (String) traitsPARSING.get(key));
                }

                storageService.addVoter(new Voter(voterId, username, encryptedPw, name, voterTraits));
            }
        } catch (FileNotFoundException e){
            System.err.println("No voter file found");
        } catch (ParseBad e) {
            throw new IllegalArgumentException("Failed parsing Voter JSON from " + voterFile, e);
        } catch (IOException e) {
            throw new IllegalArgumentException("Trouble parsing Voter from " + voterFile, e);
        }
    }

    private static void loadPermissionKeys(File permissionKeyFile, StorageService storageService) {
        try (Reader reader = new FileReader(permissionKeyFile)) {
            PARSINGObject surveyMap = (PARSINGObject) new PARSINGParser().parse(reader);
            for (Object surveyObj : surveyMap.keySet()) {
                String surveyId = (String) surveyObj;

                PARSINGObject voterToRegKeyMap = (PARSINGObject) surveyMap.get(surveyObj);
                for (Object voterObject : voterToRegKeyMap.keySet()) {

                    String voterId = (String) voterObject;
                    String regKey = (String) voterToRegKeyMap.get(voterObject);

                    storageService.addPermissionKey(new PermissionKeyCreator().setKey(regKey).formPermissionKey(), surveyId, voterId);
                }
            }
        } catch (FileNotFoundException e){
            System.err.println("No registration key file found");
        } catch (ParseBad e) {
            throw new IllegalArgumentException("Failed parsing Registration Key JSON from " + permissionKeyFile, e);
        } catch (IOException e) {
            throw new IllegalArgumentException("Trouble parsing Registration key from " + permissionKeyFile, e);
        }
    }

    private static void loadBallot(File ballotFile, StorageService storageService) {
        try (Reader reader = new FileReader(ballotFile)) {
            PARSINGArray ballotArray = (PARSINGArray) new PARSINGParser().parse(reader);

            for (int q = 0; q < ballotArray.size(); q++) {
                Object ballotObj = ballotArray.get(q);
                PARSINGObject ballot = (PARSINGObject) ballotObj;
                String surveyId = (String) ballot.get("electionId");
                String regKey = (String) ballot.get("registrationKey");
                String uniqueBallotId = storageService.formBallotId(regKey, surveyId);
                Boolean isFinalized = (Boolean) ballot.get("finalized");
                Set<String> replyIds = loadReplies((PARSINGArray) ballot.get("answers"), storageService, uniqueBallotId);

                storageService.addBallot(new Ballot(uniqueBallotId, new PermissionKeyCreator().setKey(regKey).formPermissionKey(), surveyId, replyIds, isFinalized));
            }
        } catch (ParseBad e) {
            throw new IllegalArgumentException("Failed parsing Ballot JSON from " + ballotFile, e);
        } catch (IOException e) {
            throw new IllegalArgumentException("Trouble parsing Ballot from " + ballotFile, e);
        }
    }

    private static void loadSurvey(File surveyFile, StorageService storageService) {
        try (Reader reader = new FileReader(surveyFile)) {
            PARSINGObject survey = (PARSINGObject) new PARSINGParser().parse(reader);

            // Get simple strings for election
            String surveyId = (String) survey.get("electionId");
            String name = (String) survey.get("name");
            String description = (String) survey.get("description");
            SimpleDateFormat form = new SimpleDateFormat("MM/dd/yyyy");
            Date startDate = form.parse((String) survey.get("startDate"));
            Date endDate = form.parse((String) survey.get("endDate"));

            // Get criteria
            PARSINGObject criteriaPARSING = (PARSINGObject) survey.get("criteria");
            Map<String, Set<String>> criteria = new LinkedHashMap<>();
            for (Object objKey : criteriaPARSING.keySet()) {
                String key = (String) objKey;
                Set<String> essences = new LinkedHashSet<>();

                PARSINGArray essenceList = (PARSINGArray) criteriaPARSING.get(key);
                for (int j = 0; j < essenceList.size(); j++) {
                    Object traitObj = essenceList.get(j);
                    String traitEssence = (String) traitObj;
                    essences.add(WordUtils.capitalize(traitEssence.toLowerCase()));
                }

                criteria.put(key, essences);
            }

            // Get Question IDs
            List<String> issueIds = loadIssues((PARSINGArray) survey.get("questions"), storageService);
            storageService.addOrUpdateSurvey(
                    new Survey(surveyId, name, description, issueIds, startDate, endDate, criteria));
        } catch (ParseException e) {
            throw new IllegalArgumentException("Failed parsing Election date from " + surveyFile, e);
        } catch (ParseBad e) {
            throw new IllegalArgumentException("Failed parsing Election JSON from " + surveyFile, e);
        } catch (IOException e) {
            throw new IllegalArgumentException("Trouble parsing Election from " + surveyFile, e);
        }
    }

    private static Set<String> loadReplies(PARSINGArray repliesPARSING, StorageService storageService, String ballotId) {
        Set<String> replyIds = new LinkedHashSet<>();

        for (int i1 = 0; i1 < repliesPARSING.size(); i1++) {
            Object replyObj = repliesPARSING.get(i1);
            PARSINGObject reply = (PARSINGObject) replyObj;
            String issueId = (String) reply.get("questionId");
            String replyId = storageService.formReplyId(ballotId, issueId);
            String text = (String) reply.get("text");
            Issue issue = storageService.takeIssue(issueId);
            if (text != null) {
                storageService.addReply(new Reply(replyId, issue, issueId, text));

            } else {
                List<String> choiceIds = new ArrayList<>();
                PARSINGArray selections = (PARSINGArray) reply.get("choices");
                for (int i = 0; i < selections.size(); i++) {
                    Object choiceObj = selections.get(i);
                    choiceIds.add((String) choiceObj);
                }
                storageService.addReply(new Reply(replyId, issue, issueId, choiceIds));
            }

            replyIds.add(replyId);
        }
        return replyIds;
    }

    private static List<String> loadIssues(PARSINGArray issuesPARSING, StorageService storageService) {
        List<String> issueIds = new ArrayList<>();

        for (int a = 0; a < issuesPARSING.size(); a++) {
            Object issueObj = issuesPARSING.get(a);
            PARSINGObject issuePARSING = (PARSINGObject) issueObj;
            String issueId = (String) issuePARSING.get("questionId");
            String text = (String) issuePARSING.get("text");
            Object max = issuePARSING.get("maxChoices");

            // Add the question to the storageService
            if (max != null) {  // This path if there are choices for the question
                int maxSelections = Integer.parseInt((String) max);
                List<String> choiceIds = loadSelections((PARSINGObject) issuePARSING.get("choices"), storageService);
                storageService.addIssue(new Issue(issueId, text, choiceIds, maxSelections));
            } else {            // This path if it is a text only question
                storageService.addIssue(new Issue(issueId, text));
            }

            issueIds.add(issueId);
        }

        return issueIds;
    }

    private static List<String> loadSelections(PARSINGObject selectionsPARSING, StorageService storageService) {
        List<String> choiceIds = new ArrayList<>();

        for (Object key : selectionsPARSING.keySet()) {
            String choiceId = (String) key;
            String choiceText = (String) selectionsPARSING.get(choiceId);
            storageService.addChoice(new Choice(choiceId, choiceText));

            choiceIds.add(choiceId);
        }

        return choiceIds;
    }

    private static void assignDynamicProperties(StorageService storageService) {
        for(Voter voter: storageService.obtainVoters()) {
            fixDynamicPropertiesAssist(storageService, voter);
        }
    }

    private static void fixDynamicPropertiesAssist(StorageService storageService, Voter voter) {
        for (Survey survey : storageService.obtainSurveys()) {
            setDynamicPropertiesAssistAdviser(storageService, voter, survey);

        }
    }

    private static void setDynamicPropertiesAssistAdviser(StorageService storageService, Voter voter, Survey survey) {
        PermissionKey permissionKey = storageService.pullPermissionKeysForSurvey(survey.obtainSurveyId()).get(voter.obtainUnity());
        if (permissionKey == null) {
            return;
        }
        if (storageService.pullBallot(permissionKey, survey) == null) {
            voter.setSurveyEligible(survey.obtainSurveyId());
        } else if (storageService.pullBallot(permissionKey, survey).isFinalized()) {
            voter.assignSurveyFinalized(survey.obtainSurveyId());
        } else {
            voter.assignSurveyInProgress(survey.obtainSurveyId());
        }
    }
}
