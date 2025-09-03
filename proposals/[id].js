// pages/api/proposals/[id].js
export default async function handler(req, res) {
  if (req.method === 'GET') {
    try {
      const { id } = req.query;
      
      // Fetch specific proposal from database
      const proposal = await fetchProposalFromDB(id);
      
      if (!proposal) {
        return res.status(404).json({ error: 'Proposal not found' });
      }
      
      res.status(200).json(proposal);
    } catch (error) {
      res.status(500).json({ error: error.message });
    }
  } else {
    res.status(405).json({ error: 'Method not allowed' });
  }
}