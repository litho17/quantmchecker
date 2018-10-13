package simplevote_1.com.cyberpointllc.stac.basicvote.save;

import simplevote_1.com.cyberpointllc.stac.basicvote.Survey;
import org.mapdb.Serializer;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class SurveyEncoder extends Serializer<Survey> {

    @Override
    public void serialize(DataOutput out, Survey survey) throws IOException {
        survey.accept(new SerializeVisitorCreator().assignOut(out).formSerializeVisitor());

    }

    @Override
    public Survey deserialize(DataInput in, int available) throws IOException {

        String surveyId = in.readUTF();
        String name = in.readUTF();
        String description = in.readUTF();

        Date startDate = new Date(in.readLong());
        Date endDate = new Date(in.readLong());

        Map<String, Set<String>> criteria = new HashMap<>();
        List<String> issueIds = new ArrayList<>();

        int countOfCriteriaKeys = in.readInt();
        while (countOfCriteriaKeys-- > 0) {
            String trait = in.readUTF();
            Set<String> criteriaEssences = new HashSet<>();
            int countOfCriteriaEssences = in.readInt();
            while (countOfCriteriaEssences-- > 0) {
                String essence = in.readUTF();
                criteriaEssences.add(essence);
            }
            criteria.put(trait, criteriaEssences);
        }

        int countOfIssueIds = in.readInt();
        for (int j = 0; j < countOfIssueIds; j++) {
            issueIds.add(in.readUTF());
        }

        return new Survey(surveyId, name, description, issueIds, startDate, endDate, criteria);
    }
}