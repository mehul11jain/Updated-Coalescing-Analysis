#include "FunctionWithGPG.h"
#include "GPB.h"
#include "GPU.h"
#include "GPG.h"
#include "IndirectionList.h"
#include "Partition.h"
#include "Util.h"
#include "llvm/ADT/Twine.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Metadata.h"
#include <iostream>
#include <stack>

// ------------------------------------------------- My Implementation ----------------------------//
void FunctionWithGPG::UpdatedCoalescingAnalysis()
{

    // Initialize the Col Map in  the GPB.
    map<long, GPB *> GPBs = summary->getGPBMap();
#ifdef VERBOSE_LEVEL
#if VERBOSE_LEVEL == 11
    std::cout << "\n-------------------------- ColMap create based on Data dependency -----------------------\n\n";
#endif
#endif
    for (auto gpb = GPBs.begin(); gpb != GPBs.end(); gpb++)
    {

        map<GPB *, bool> &Colmap = (*gpb).second->getColmap();

        (*gpb).second->setDescendants();
        (*gpb).second->setAncestors();
        set<GPB *, GPBComp> desc, anc;
        desc = (*gpb).second->getDescendants();
        anc = (*gpb).second->getAncestors();

        for (auto it = GPBs.begin(); it != GPBs.end(); it++)
        {
            // std::cout << desc.size() << "---" << anc.size() << std::endl;
            if (it != gpb && (gpb == GPBs.begin() || it == GPBs.begin() || it == --GPBs.end() || gpb == --GPBs.end()))
            {
                Colmap[(*it).second] = false;
            }
            else if (desc.find((*it).second) == desc.end() && anc.find((*it).second) == anc.end() && it != gpb)
            {
                Colmap[(*it).second] = true;
            }
            else if (desc.find((*it).second) != desc.end() && it != gpb)
            {
                Colmap[(*it).second] = !((*gpb).second->DDep((*it).second));
            }
            else if (anc.find((*it).second) != anc.end() && it != gpb)
            {
                Colmap[(*it).second] = !((*it).second->DDep((*gpb).second));
            }
        }
#ifdef VERBOSE_LEVEL
#if VERBOSE_LEVEL == 11
        (*gpb).second->printColmap();
#endif
#endif
    }
#ifdef VERBOSE_LEVEL
#if VERBOSE_LEVEL == 11
    std::cout << "\n-----------------------------------------------------------------------------------------\n";
#endif
#endif
    vector<GPB *> bfs_order = get_bfs_order();

// print bfs order traversal for debug.
#ifdef VERBOSE_LEVEL
#if VERBOSE_LEVEL == 11
    std::cout << "BFS Order of traversal : ";
    for (auto it = bfs_order.begin(); it != bfs_order.end(); it++)
    {
        std::cout << (*it)->getGPBNo() << " ";
    }
    std::cout << "\n";
#endif
#endif
    vector<Partition *> parts = create_partition(bfs_order);
#ifdef VERBOSE_LEVEL
#if VERBOSE_LEVEL == 11
    cout << "\n-------------- Partition created after Coalescing Analysis ------------------------------\n\n";
    cout << "pi = { ";
    for (auto part = parts.begin(); part != parts.end(); part++)
    {
        set<GPB *, GPBComp> gpbs = (*part)->getGPBs();
        cout << "{";
        for (auto it = gpbs.begin(); it != gpbs.end(); it++)
        {
            if (it != gpbs.begin())
                cout << ", ";
            cout << (*it)->getGPBNo();
        }
        if (part != --parts.end())
            cout << "}, ";
        else
            cout << "} ";
    }
    cout << " }";
    cout << "\n\n-----------------------------------------------------------------------------------------\n";
#endif
#endif
    for (auto part : parts)
    {
        part->setEntryNodesOfPartition(summary);
        part->setExitNodesOfPartition(summary);
    }

    map<GPB *, Partition *> GPBToPart;
    for (auto i : parts)
    {
        set<GPB *, GPBComp> GPBsofPart = i->getGPBs();
        for (auto it : GPBsofPart)
        {
            GPBToPart[(it)] = i;
        }
    }
    ConnectParts(parts, GPBToPart);
#ifdef VERBOSE_LEVEL
#if VERBOSE_LEVEL == 11
    set<GPB *, GPBComp> GPBsAfterCoalescing = summary_after_updated_coalescing->getGPBSet();
    cout << "\nGPBs after Coalescing :\n";
    for (auto it = GPBsAfterCoalescing.begin(); it != GPBsAfterCoalescing.end(); it++)
    {
        (*it)->print();
        set<GPUNode *, GPUNodeComp> maydefset = (*it)->getMayDefSet();
        cout << "MayDefSet : {";
        for (auto gpuNode : maydefset)
        {
            cout << "(" << gpuNode->getNameOfVariable().str() << ", " << gpuNode->getIndirectList()->getIndirectionLevel() << "), ";
        }
        cout << "}\n\n";
    }
#endif
#endif
}

vector<Partition *> FunctionWithGPG::create_partition(vector<GPB *> bfs_order)
{

    vector<Partition *> Result;
    map<GPB *, bool> visited;
    map<GPB *, Partition *> GPBtoPart;

    for (auto gpb = bfs_order.begin(); gpb != bfs_order.end(); gpb++)
    {
        if (visited[(*gpb)] == false)
        {
            // cout << (*gpb)->getGPBNo() << "\n";
            Partition *curr_part = new Partition({}, summary);
            curr_part->addGPBtopart((*gpb));

            stack<set<GPB *, GPBComp>> coherent_part;
            coherent_part.push(curr_part->getGPBs());

            queue<GPB *> q;
            q.push((*gpb));
            visited[(*gpb)] = true;
            while (!q.empty())
            {

                // Get the Last added GPB in the part and extend the part using the succs and preds of the GPB.
                GPB *curr = q.front();
                q.pop();
                // curr->print();

                set<GPB *, GPBComp> succ, preds;
                succ = curr->getAllSuccessors();
                preds = curr->getAllPredecessors();
                map<GPB *, bool> Col = curr->getColmap();

                // Iterate over preds and extend the partition.
                vector<Partition *> partsToRemoveifCoherent;
                bool has_merged_allocated_parts = false;
                for (auto it = preds.begin(); it != preds.end(); it++)
                {
                    if (Col[(*it)] == true)
                    {
                        if (visited[(*it)] == false)
                        {
                            set<GPB *, GPBComp> GPBsinPart = curr_part->getGPBs();
                            map<GPB *, bool> Col = (*it)->getColmap();
                            bool status = true;
                            for (auto i = GPBsinPart.begin(); i != GPBsinPart.end(); i++)
                            {
                                if (Col[(*i)] != true)
                                {
                                    status = false;
                                    break;
                                }
                            }
                            if (status)
                                curr_part->addGPBtopart((*it));
                        }
                    }
                }

                // Iterate over succ and extend the partition.
                for (auto it = succ.begin(); it != succ.end(); it++)
                {
                    if (Col[*it] == true)
                    {
                        if (visited[(*it)] == false)
                        {
                            set<GPB *, GPBComp> GPBsinPart = curr_part->getGPBs();
                            map<GPB *, bool> Col = (*it)->getColmap();
                            bool status = true;
                            for (auto i = GPBsinPart.begin(); i != GPBsinPart.end(); i++)
                            {
                                if (Col[(*i)] != true)
                                {
                                    status = false;
                                    break;
                                }
                            }
                            if (status)
                                curr_part->addGPBtopart((*it));
                        }
                    }
                }
                // Check Coherence of the part create
                set<GPB *, GPBComp> entryNodes = curr_part->findEntryNodesOfPartition();
                set<GPB *, GPBComp> exitNodes = curr_part->findExitNodesOfPartition();

                if (curr_part->isCoherent(entryNodes, exitNodes))
                {
                    if (has_merged_allocated_parts)
                    {
                        vector<Partition *> new_result;
                        for (auto it : Result)
                        {
                            if (find(partsToRemoveifCoherent.begin(), partsToRemoveifCoherent.end(), it) == partsToRemoveifCoherent.end())
                            {
                                new_result.push_back(it);
                            }
                        }
                        Result = new_result;
                    }
                    Partition *new_part = new Partition(curr_part->getGPBs(), summary);
                    if (!coherent_part.empty())
                        coherent_part.pop();
                    delete curr_part;
                    coherent_part.push(new_part->getGPBs());
                    curr_part = new_part;
                }

                for (auto x : curr_part->getGPBs())
                {
                    if (visited[x] == false)
                    {
                        q.push(x);
                    }
                    visited[x] = true;
                }
            }
            set<GPB *, GPBComp> entryNodes = curr_part->findEntryNodesOfPartition();
            set<GPB *, GPBComp> exitNodes = curr_part->findExitNodesOfPartition();
            if (!(curr_part->isCoherent(entryNodes, exitNodes)))
            {
                set<GPB *, GPBComp> GPBsOfCurr = curr_part->getGPBs();
                set<GPB *, GPBComp> LastCoherentPartGPBs = coherent_part.top();
                for (auto gpb : GPBsOfCurr)
                {
                    if (LastCoherentPartGPBs.find(gpb) == LastCoherentPartGPBs.end())
                    {
                        visited[gpb] = false;
                    }
                }
                delete curr_part;
                curr_part = new Partition(coherent_part.top(), summary);
            }
            for (auto it : curr_part->getGPBs())
                GPBtoPart[it] = curr_part;
            Result.push_back(curr_part);
        }
    }

    return Result;
}

vector<GPB *> FunctionWithGPG::get_bfs_order()
{
    vector<GPB *> Result;
    map<GPB *, bool> visited;
    queue<GPB *> q;

    map<long, GPB *> GPBs = (*summary).getGPBMap();
    GPB *Start = (*GPBs.begin()).second;
    q.push(Start);

    while (!q.empty())
    {
        GPB *curr = q.front();
        q.pop();
        Result.push_back(curr);
        visited[curr] = 1;
        set<GPB *, GPBComp> succ = curr->getAllSuccessors();
        for (auto it = succ.begin(); it != succ.end(); it++)
        {
            if (visited[(*it)] == false)
            {
                q.push(*it);
                visited[*it] = true;
            }
        }
    }
    return Result;
}

void FunctionWithGPG::ConnectParts(vector<Partition *> parts, map<GPB *, Partition *> GPBsToPart)
{

    map<Partition *, GPB *> NewGPBofEachPart;
    summary_after_updated_coalescing = new GPG();
    for (auto it = parts.begin(); it != parts.end(); it++)
    {
        GPB *gpb;
        set<GPB *, GPBComp> GPBsofPart = (*it)->getGPBs();
        set<GPU *, GPUComp> GPUsofNewGPB;
        for (auto i = GPBsofPart.begin(); i != GPBsofPart.end(); i++)
        {
            set<GPU *, GPUComp> GPUsofGPBofPart = (*i)->getGPUSet();
            for (auto i1 : GPUsofGPBofPart)
            {
                GPUsofNewGPB.insert(i1);
            }
        }
        gpb = new GPB(GPUsofNewGPB);
        set<GPUNode *, GPUNodeComp> maydefset = (*it)->mayDefSetsOfPartition();
        gpb->setMayDefSet(maydefset);
        NewGPBofEachPart[(*it)] = gpb;
    }

    map<Partition *, set<Partition *>> Partsuccs, Partpreds;
    for (auto it = parts.begin(); it != parts.end(); it++)
    {
        set<GPB *, GPBComp> GPBsofPart = (*it)->getGPBs();
        for (auto i : GPBsofPart)
        {
            set<GPB *, GPBComp> succs, preds;
            succs = (i)->getAllSuccessors();
            preds = (i)->getAllPredecessors();
            for (auto succ : succs)
            {
                if (*it != GPBsToPart[succ])
                    Partsuccs[(*it)].insert(GPBsToPart[succ]);
            }
            for (auto pred : preds)
            {
                if (*it != GPBsToPart[pred])
                    Partpreds[(*it)].insert(GPBsToPart[pred]);
            }
        }
    }

    for (auto it = parts.begin(); it != parts.end(); it++)
    {
        set<Partition *> succs, preds;
        succs = Partsuccs[(*it)];
        preds = Partpreds[(*it)];
        for (auto succ : succs)
        {
            NewGPBofEachPart[(*it)]->addSuccessor(NewGPBofEachPart[succ]);
            summary_after_updated_coalescing->addEdge(NewGPBofEachPart[(*it)]->getGPBNo(), NewGPBofEachPart[succ]->getGPBNo());
        }
        for (auto pred : preds)
        {
            NewGPBofEachPart[(*it)]->addPredecessor(NewGPBofEachPart[pred]);
            summary_after_updated_coalescing->addEdge(NewGPBofEachPart[(*it)]->getGPBNo(), NewGPBofEachPart[pred]->getGPBNo());
        }
    }
    for (auto it : NewGPBofEachPart)
    {
        summary_after_updated_coalescing->insertGPB(it.second);
    }
    summary_after_updated_coalescing->setEntryNode(NewGPBofEachPart[parts[0]]);
    summary_after_updated_coalescing->setExitNode(NewGPBofEachPart[parts[parts.size() - 1]]);

    string funName = fun->getName();
    string dotFileName = funName + "gpgAfterUpdatedCoalescing.dot";
    summary_after_updated_coalescing->printToDot(dotFileName);
    summary = summary_after_updated_coalescing;
}

GPG *FunctionWithGPG::getSummaryAfterUpdatedCoalescing()
{
    return summary_after_updated_coalescing;
}
// -----------------------------------------------------------------------------------------------//

//-------------------------------------------------- My Implementation ------------------------------------//
void GPB::printColmap()
{
    // std::cout << "---------------------------------------ColMap for the current GPB:----------------------------------------\n";
    std::cout << "Col " << gpbNo << ": { ";
    for (auto it = Col.begin(); it != Col.end(); it++)
    {
        if (it != Col.begin())
            std::cout << ", ";
        std::cout << (*it).first->getGPBNo() << " -> " << (*it).second;
    }
    std::cout << " }\n";
    // std::cout << "------------------------------------------------------------------------------------------------------------";
}

map<GPB *, bool> &GPB::getColmap()
{
    return Col;
}
void GPB::setColmap(GPB *gpb, bool b)
{
    Col[gpb] = b;
}

bool GPB::DDep(GPB *delta2)
{

    GPB *delta1 = this;
    set<GPU *, GPUComp> gpus1 = delta1->getGPUSet();
    set<GPU *, GPUComp> gpus2 = delta2->getGPUSet();
    for (auto it = gpus1.begin(); it != gpus1.end(); it++)
    {

        Type *gamma_1 = (*it)->typeOfDefinedVariable();
        if (gamma_1 == NULL)
            return false;
        string result_1, type_info_1;
        raw_string_ostream rso_1(type_info_1);
        gamma_1->print(rso_1);
        result_1 = rso_1.str();

        for (auto i = gpus2.begin(); i != gpus2.end(); i++)
        {
            if ((*it)->isGPUIndirectlyDefinesVariable())
            {

                Type *gamma_2 = (*i)->typeOfDefinedVariable();
                if (gamma_2 == NULL)
                    return false;
                string result_2, type_info_2;
                raw_string_ostream rso_2(type_info_2);

                gamma_2->print(rso_2);
                result_2 = rso_2.str();
                if (result_1 == result_2)
                    return true;

                pair<set<char *, StringComp>, set<char *, StringComp>> TRef = (*i)->typesOfDirectIndirectReferences();
                set<char *, StringComp> TDirectRef = TRef.first;
                set<char *, StringComp> TInDirectRef = TRef.second;

                for (auto t1 = TDirectRef.begin(); t1 != TDirectRef.end(); t1++)
                {
                    result_2 = *t1;
                    if (result_1 == result_2)
                        return true;
                }
                for (auto t2 = TInDirectRef.begin(); t2 != TInDirectRef.end(); t2++)
                {
                    result_2 = *t2;
                    if (result_1 == result_2)
                        return true;
                }
            }
            else
            {
                if ((*i)->isGPUIndirectlyDefinesVariable())
                {
                    Type *gamma_2 = (*i)->typeOfDefinedVariable();
                    if (gamma_2 == NULL)
                        return false;
                    string result_2, type_info_2;
                    raw_string_ostream rso_2(type_info_2);
                    gamma_2->print(rso_2);
                    result_2 = rso_2.str();
                    if (result_1 == result_2)
                        return true;
                }
                pair<set<char *, StringComp>, set<char *, StringComp>> TRef = (*i)->typesOfDirectIndirectReferences();
                set<char *, StringComp> TInDirectRef = TRef.second;

                for (auto t2 = TInDirectRef.begin(); t2 != TInDirectRef.end(); t2++)
                {
                    string result_2 = *t2;
                    if (result_1 == result_2)
                        return true;
                }
            }
            if ((*i)->undesirableComposition(1, *it))
            {
                return true;
            }
        }
    }
    return false;
}

void GPB::setDescendants()
{
    GPB *curr_node = this;
    std::queue<GPB *> q;
    std::map<GPB *, bool> visited;
    q.push(curr_node);
    visited[curr_node] = true;
    while (!q.empty())
    {
        GPB *curr = q.front();
        q.pop();

        if (curr != curr_node)
        {
            descendants.insert(curr);
        }

        set<GPB *, GPBComp> successors = curr->getAllSuccessors();
        for (auto it = successors.begin(); it != successors.end(); it++)
        {
            if (visited[(*it)] == false)
            {
                q.push(*it);
                visited[*it] = true;
            }
        }
    }
}
void GPB::setAncestors()
{
    GPB *curr_node = this;
    std::queue<GPB *> q;
    map<GPB *, bool> visited;
    q.push(curr_node);
    visited[curr_node] = true;
    while (!q.empty())
    {

        GPB *curr = q.front();
        q.pop();

        if (curr != curr_node)
        {
            ancestors.insert(curr);
        }

        set<GPB *, GPBComp> predecessors = curr->getAllPredecessors();
        for (auto it = predecessors.begin(); it != predecessors.end(); it++)
        {
            if (visited[(*it)] == false)
            {
                q.push(*it);
                visited[curr] = true;
            }
        }
    }
}
set<GPB *, GPBComp> GPB::getAncestors()
{
    return ancestors;
}
set<GPB *, GPBComp> GPB::getDescendants()
{
    return descendants;
}

set<GPB *, GPBComp> GPB::findExternalPreds(set<GPB *, GPBComp> part)
{
    set<GPB *, GPBComp> externalPreds, GPBsofPart = part;
    set<long> GPBsIDofPart;
    for (auto it = GPBsofPart.begin(); it != GPBsofPart.end(); it++)
    {
        GPBsIDofPart.insert((*it)->getGPBNo());
    }
    for (auto it = preds.begin(); it != preds.end(); it++)
    {
        if (GPBsIDofPart.find((*it)->getGPBNo()) == GPBsIDofPart.end())
        {
            externalPreds.insert((*it));
        }
    }
    return externalPreds;
}
set<GPB *, GPBComp> GPB::findExternalSuccs(set<GPB *, GPBComp> part)
{
    set<GPB *, GPBComp> externalSuccs, GPBsofPart = part;
    set<long> GPBsIDofPart;
    for (auto it = GPBsofPart.begin(); it != GPBsofPart.end(); it++)
    {
        GPBsIDofPart.insert((*it)->getGPBNo());
    }
    for (auto it = succs.begin(); it != succs.end(); it++)
    {
        if (GPBsIDofPart.find((*it)->getGPBNo()) == GPBsIDofPart.end())
        {
            externalSuccs.insert((*it));
        }
    }
    return externalSuccs;
}

//--------------------------------------------------------------------------------------------------------//
// -------------------------------------------------- My Implementation -------------------------------------//
void Partition::addGPBtopart(GPB *gpb)
{
    gpbs.insert(gpb);
}

set<GPB *, GPBComp> Partition::findEntryNodesOfPartition()
{

    set<GPB *, GPBComp> EntryNodes;
    set<long> GPBsOfPart;

    for (auto gpb = gpbs.begin(); gpb != gpbs.end(); gpb++)
    {
        GPBsOfPart.insert((*gpb)->getGPBNo());
    }

    for (auto gpb = gpbs.begin(); gpb != gpbs.end(); gpb++)
    {

        bool hasExternalpred = false;

        set<GPB *, GPBComp> preds = (*gpb)->getAllPredecessors();
        for (auto it = preds.begin(); it != preds.end(); it++)
        {

            long GPBno = (*it)->getGPBNo();
            if (GPBsOfPart.find(GPBno) == GPBsOfPart.end())
            {
                hasExternalpred = true;
                break;
            }
        }
        if (hasExternalpred)
            EntryNodes.insert((*gpb));
    }
    return EntryNodes;
}
set<GPB *, GPBComp> Partition::findExitNodesOfPartition()
{

    set<GPB *, GPBComp> ExitNodes;
    set<long> GPBsOfPart;

    for (auto gpb = gpbs.begin(); gpb != gpbs.end(); gpb++)
    {
        GPBsOfPart.insert((*gpb)->getGPBNo());
    }

    for (auto gpb = gpbs.begin(); gpb != gpbs.end(); gpb++)
    {

        bool hasExternalsucc = false;

        set<GPB *, GPBComp> succs = (*gpb)->getAllSuccessors();
        for (auto it = succs.begin(); it != succs.end(); it++)
        {

            long GPBno = (*it)->getGPBNo();
            if (GPBsOfPart.find(GPBno) == GPBsOfPart.end())
            {
                hasExternalsucc = true;
                break;
            }
        }
        if (hasExternalsucc)
            ExitNodes.insert((*gpb));
    }
    return ExitNodes;
}
bool Partition::isCoherent(set<GPB *, GPBComp> EntryNodes, set<GPB *, GPBComp> ExitNodes)
{
    bool status = true;

    // check for Entry Nodes.
    for (auto it = EntryNodes.begin(); it != EntryNodes.end(); it++)
    {
        for (auto i = EntryNodes.begin(); i != EntryNodes.end(); i++)
        {
            if (it != i)
            {
                set<GPB *, GPBComp> externalPreds1 = (*it)->findExternalPreds(gpbs);
                set<GPB *, GPBComp> externalPreds2 = (*i)->findExternalPreds(gpbs);

                // cout << "Size1 : " << externalPreds1.size() << "\n";
                // cout << "Size2 : " << externalPreds2.size() << "\n";

                // cout << "xPred1 : " << (*externalPreds1.begin())->getGPBNo() << "\n";
                // cout << "xPred2 : " << (*externalPreds2.begin())->getGPBNo() << "\n";

                set<long> externalPredsGPBids1, externalPredsGPBids2;
                for (auto pred1 : externalPreds1)
                    externalPredsGPBids1.insert(pred1->getGPBNo());
                for (auto pred2 : externalPreds2)
                    externalPredsGPBids2.insert(pred2->getGPBNo());

                if (externalPreds1.size() != externalPreds2.size())
                    return false;
                for (auto i2 = externalPredsGPBids1.begin(); i2 != externalPredsGPBids1.end(); i2++)
                {
                    // cout << (*i2) << endl;
                    if (externalPredsGPBids2.find((*i2)) == externalPredsGPBids2.end())
                    {
                        return false;
                    }
                }
            }
        }
    }
    // Check for exit Nodes.
    for (auto it = ExitNodes.begin(); it != ExitNodes.end(); it++)
    {
        for (auto i = ExitNodes.begin(); i != ExitNodes.end(); i++)
        {
            if (it != i)
            {
                set<GPB *, GPBComp> externalSuccs1 = (*it)->findExternalSuccs(gpbs);
                set<GPB *, GPBComp> externalSuccs2 = (*i)->findExternalSuccs(gpbs);

                set<long> externalSuccsGPBids1, externalSuccsGPBids2;
                for (auto succ1 : externalSuccs1)
                    externalSuccsGPBids1.insert(succ1->getGPBNo());
                for (auto succ2 : externalSuccs2)
                    externalSuccsGPBids2.insert(succ2->getGPBNo());

                if (externalSuccs1.size() != externalSuccs2.size())
                    return false;
                for (auto i2 = externalSuccsGPBids1.begin(); i2 != externalSuccsGPBids1.end(); i2++)
                {
                    if (externalSuccsGPBids2.find((*i2)) == externalSuccsGPBids2.end())
                    {
                        return false;
                    }
                }
            }
        }
    }
    return status;
}
// ----------------------------------------------------------------------------------------------------------//
